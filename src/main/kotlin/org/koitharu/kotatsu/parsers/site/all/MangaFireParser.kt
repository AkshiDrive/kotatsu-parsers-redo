package org.koitharu.kotatsu.parsers.site.all

import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.delay
import okhttp3.HttpUrl.Companion.toHttpUrl
import okhttp3.Interceptor
import org.jsoup.Jsoup
import org.jsoup.nodes.Document
import org.koitharu.kotatsu.parsers.MangaLoaderContext
import org.koitharu.kotatsu.parsers.MangaParserAuthProvider
import org.koitharu.kotatsu.parsers.MangaSourceParser
import org.koitharu.kotatsu.parsers.bitmap.Rect
import org.koitharu.kotatsu.parsers.config.ConfigKey
import org.koitharu.kotatsu.parsers.core.PagedMangaParser
import org.koitharu.kotatsu.parsers.model.ContentRating
import org.koitharu.kotatsu.parsers.model.Manga
import org.koitharu.kotatsu.parsers.model.MangaChapter
import org.koitharu.kotatsu.parsers.model.MangaListFilter
import org.koitharu.kotatsu.parsers.model.MangaListFilterCapabilities
import org.koitharu.kotatsu.parsers.model.MangaListFilterOptions
import org.koitharu.kotatsu.parsers.model.MangaPage
import org.koitharu.kotatsu.parsers.model.MangaParserSource
import org.koitharu.kotatsu.parsers.model.MangaState
import org.koitharu.kotatsu.parsers.model.MangaTag
import org.koitharu.kotatsu.parsers.model.RATING_UNKNOWN
import org.koitharu.kotatsu.parsers.model.SortOrder
import org.koitharu.kotatsu.parsers.network.OkHttpWebClient
import org.koitharu.kotatsu.parsers.network.WebClient
import org.koitharu.kotatsu.parsers.util.attrAsAbsoluteUrl
import org.koitharu.kotatsu.parsers.util.attrAsRelativeUrl
import org.koitharu.kotatsu.parsers.util.generateUid
import org.koitharu.kotatsu.parsers.util.getCookies
import org.koitharu.kotatsu.parsers.util.mapChapters
import org.koitharu.kotatsu.parsers.util.mapNotNullToSet
import org.koitharu.kotatsu.parsers.util.nullIfEmpty
import org.koitharu.kotatsu.parsers.util.ownTextOrNull
import org.koitharu.kotatsu.parsers.util.parseFailed
import org.koitharu.kotatsu.parsers.util.parseHtml
import org.koitharu.kotatsu.parsers.util.parseJson
import org.koitharu.kotatsu.parsers.util.parseSafe
import org.koitharu.kotatsu.parsers.util.selectFirstOrThrow
import org.koitharu.kotatsu.parsers.util.splitByWhitespace
import org.koitharu.kotatsu.parsers.util.suspendlazy.suspendLazy
import org.koitharu.kotatsu.parsers.util.toAbsoluteUrl
import org.koitharu.kotatsu.parsers.util.toTitleCase
import org.koitharu.kotatsu.parsers.util.urlEncoded
import java.text.SimpleDateFormat
import java.security.SecureRandom
import java.security.cert.X509Certificate
import java.util.Base64
import java.util.EnumSet
import java.util.Locale
import javax.net.ssl.SSLContext
import javax.net.ssl.SSLSocketFactory
import javax.net.ssl.TrustManager
import javax.net.ssl.X509TrustManager
import kotlin.math.min
import kotlin.random.Random

private const val PIECE_SIZE = 200
private const val MIN_SPLIT_COUNT = 5
private const val VRF_RETRY_ATTEMPTS = 4 // Total attempts (1 initial + 3 retries)
private const val VRF_INITIAL_DELAY_MS = 1500L // Start with a longer delay
private const val VRF_MAX_DELAY_MS = 8000L // Cap the delay to 8 seconds
private const val VRF_BACKOFF_FACTOR = 2.0

@Suppress("CustomX509TrustManager")
internal abstract class MangaFireParser(
    context: MangaLoaderContext,
    source: MangaParserSource,
    private val siteLang: String,
) : PagedMangaParser(context, source, 30), Interceptor, MangaParserAuthProvider {

    // VRF cache removed - each request gets its own unique token to prevent 403 errors
    private val vrfValidityMs = 12 * 60 * 60 * 1000L // 12 hours

    private val client: WebClient by lazy {
        val newHttpClient = context.httpClient.newBuilder()
            .sslSocketFactory(SSLUtils.sslSocketFactory!!, SSLUtils.trustManager)
            .hostnameVerifier { _, _ -> true }
            .addInterceptor { chain ->
                val request = chain.request()
                val response = chain.proceed(request.newBuilder()
                    .addHeader("Referer", "https://$domain/")
                    .build())

                if (request.url.fragment?.startsWith("scrambled") == true) {
                    return@addInterceptor context.redrawImageResponse(response) { bitmap ->
                        val offset = request.url.fragment!!.substringAfter("_").toInt()
                        val width = bitmap.width
                        val height = bitmap.height

                        val result = context.createBitmap(width, height)

                        val pieceWidth = min(PIECE_SIZE, width.ceilDiv(MIN_SPLIT_COUNT))
                        val pieceHeight = min(PIECE_SIZE, height.ceilDiv(MIN_SPLIT_COUNT))
                        val xMax = width.ceilDiv(pieceWidth) - 1
                        val yMax = height.ceilDiv(pieceHeight) - 1

                        for (y in 0..yMax) {
                            for (x in 0..xMax) {
                                val xDst = pieceWidth * x
                                val yDst = pieceHeight * y
                                val w = min(pieceWidth, width - xDst)
                                val h = min(pieceHeight, height - yDst)

                                val xSrc = pieceWidth * when (x) {
                                    xMax -> x // margin
                                    else -> (xMax - x + offset) % xMax
                                }
                                val ySrc = pieceHeight * when (y) {
                                    yMax -> y // margin
                                    else -> (yMax - y + offset) % yMax
                                }

                                val srcRect = Rect(xSrc, ySrc, xSrc + w, ySrc + h)
                                val dstRect = Rect(xDst, yDst, xDst + w, yDst + h)

                                result.drawBitmap(bitmap, srcRect, dstRect)
                            }
                        }

                        result
                    }
                }

                response
            }
            .build()
        OkHttpWebClient(newHttpClient, source)
    }

    private val vrfParamRegex = Regex("[?&]vrf=([^&]+)")

    // Result holder for retry helpers (kept private to this parser)
    private data class RetryOutcome<T>(
        val value: T?,
        val error: Throwable?,
    )

    // New backoff-based retry (kept private to avoid exposing private type)
    private suspend fun <T> retryWithBackoff(
        attempts: Int = VRF_RETRY_ATTEMPTS,
        initialDelayMs: Long = VRF_INITIAL_DELAY_MS,
        maxDelayMs: Long = VRF_MAX_DELAY_MS,
        backoffFactor: Double = VRF_BACKOFF_FACTOR,
        block: suspend (attempt: Int) -> T?,
    ): RetryOutcome<T> {
        var lastError: Throwable? = null
        var currentDelay = initialDelayMs

        for (attempt in 1..attempts) {
            try {
                val result = block(attempt)
                if (result != null) {
                    return RetryOutcome(result, null)
                }
            } catch (e: Throwable) {
                lastError = e
            }

            if (attempt == attempts) break
            val jitter = (currentDelay * 0.25 * Random.nextDouble()).toLong()
            val effectiveDelay = currentDelay + jitter
            delay(effectiveDelay)
            currentDelay = (currentDelay * backoffFactor).toLong().coerceAtMost(maxDelayMs)
        }
        return RetryOutcome(null, lastError)
    }

    // Compatibility wrapper for existing call sites; uses the new retryWithBackoff under the hood.
    private suspend fun <T> retryUntilNotNull(
        attempts: Int = VRF_RETRY_ATTEMPTS,
        delayMs: Long = VRF_INITIAL_DELAY_MS,
        maxDelayMs: Long = VRF_MAX_DELAY_MS,
        backoffFactor: Double = VRF_BACKOFF_FACTOR,
        block: suspend (attempt: Int) -> T?,
    ): RetryOutcome<T> = retryWithBackoff(
        attempts = attempts,
        initialDelayMs = delayMs,
        maxDelayMs = maxDelayMs,
        backoffFactor = backoffFactor,
        block = block,
    )

    private fun extractVrfFromUrls(urls: List<String>): String? {
        return urls.firstNotNullOfOrNull { url ->
            vrfParamRegex.find(url)?.groupValues?.getOrNull(1)
        }
    }

    override val configKeyDomain: ConfigKey.Domain = ConfigKey.Domain("mangafire.to")

    override val availableSortOrders: Set<SortOrder> = EnumSet.of(
        SortOrder.UPDATED,
        SortOrder.POPULARITY,
        SortOrder.RATING,
        SortOrder.NEWEST,
        SortOrder.ALPHABETICAL,
        SortOrder.RELEVANCE,
    )

    override fun onCreateConfig(keys: MutableCollection<ConfigKey<*>>) {
        super.onCreateConfig(keys)
        keys.add(userAgentKey)
        keys.add(ConfigKey.DisableUpdateChecking(defaultValue = true))
    }

    override val authUrl: String
        get() = "https://${domain}"

    override suspend fun isAuthorized(): Boolean {
        return context.cookieJar.getCookies(domain).any {
            it.value.contains("user")
        }
    }

    override suspend fun getUsername(): String {
        val body = client.httpGet("https://${domain}/user/profile").parseHtml().body()
        return body.selectFirst("form.ajax input[name*=username]")?.attr("value")
            ?: body.parseFailed("Cannot find username")
    }

    private val tags = suspendLazy(soft = true) {
        client.httpGet("https://$domain/filter").parseHtml()
            .select(".genres > li").map {
                MangaTag(
                    title = it.selectFirstOrThrow("label").ownText().toTitleCase(sourceLocale),
                    key = it.selectFirstOrThrow("input").attr("value"),
                    source = source,
                )
            }.associateBy { it.title }
    }

    override val filterCapabilities: MangaListFilterCapabilities
        get() = MangaListFilterCapabilities(
            isMultipleTagsSupported = true,
            isTagsExclusionSupported = true,
            isSearchSupported = true,
        )

    override suspend fun getFilterOptions() = MangaListFilterOptions(
        availableTags = tags.get().values.toSet(),
        availableStates = EnumSet.of(
            MangaState.ONGOING,
            MangaState.FINISHED,
            MangaState.ABANDONED,
            MangaState.PAUSED,
            MangaState.UPCOMING,
        ),
    )

    /**
     * Extract VRF token for chapter listings from a chapter page (where VRF is actually generated)
     * Pattern: /ajax/read/{mangaId}/{type}/{lang}?vrf=xxx
     */
    private suspend fun extractChapterListVrf(mangaId: String, type: String, langCode: String): String {
        // Try most common chapter options first for faster loading
        val chapterOptions = listOf("1", "0", "2") // Optimized: try only most common numbers first

        val mangaIdPart = mangaId.substringAfterLast('.')

        val primaryPattern = Regex("/ajax/read/$mangaIdPart/$type/$langCode\\?vrf=([^&]+)")
        val fallbackPattern = Regex("/ajax/read/[^/]+/$type/$langCode\\?vrf=([^&]+)")
        var lastError: Throwable? = null

        for (chapterNum in chapterOptions) {
            val chapterUrl = "https://$domain/read/$mangaId/$langCode/$type-$chapterNum"

            val primaryOutcome = retryUntilNotNull {
                val vrfUrls = context.captureWebViewUrls(
                    pageUrl = chapterUrl,
                    urlPattern = primaryPattern,
                    timeout = 2000L,
                )
                extractVrfFromUrls(vrfUrls)
            }
            primaryOutcome.value?.let { return it }
            lastError = primaryOutcome.error ?: lastError

            val fallbackOutcome = retryUntilNotNull {
                val fallbackUrls = context.captureWebViewUrls(
                    pageUrl = chapterUrl,
                    urlPattern = fallbackPattern,
                    timeout = 1000L,
                )
                extractVrfFromUrls(fallbackUrls)
            }
            fallbackOutcome.value?.let { return it }
            lastError = fallbackOutcome.error ?: lastError
        }

        val message = "Unable to extract chapter list VRF for $mangaId/$type/$langCode from chapter pages"
        lastError?.let { throw Exception(message, it) }
        throw Exception(message)
    }

    /**
     * Extract VRF token for individual chapter images from the actual chapter page
     * Pattern: /ajax/read/chapter/{chapterId}?vrf=xxx
     */
    private suspend fun extractChapterImagesVrf(chapterId: String, mangaId: String, type: String, langCode: String, chapterNumber: Float): String {
        val chapterNumberStr = if (chapterNumber == chapterNumber.toInt().toFloat()) {
            chapterNumber.toInt().toString()
        } else {
            chapterNumber.toString()
        }
        val chapterUrl = "https://$domain/read/$mangaId/$langCode/$type-$chapterNumberStr"

        val primaryPattern = Regex("/ajax/read/chapter/$chapterId\\?vrf=([^&]+)")
        val fallbackPattern = Regex("/ajax/read/chapter/\\d+\\?vrf=([^&]+)")
        var lastError: Throwable? = null

        val primaryOutcome = retryUntilNotNull {
            val vrfUrls = context.captureWebViewUrls(
                pageUrl = chapterUrl,
                urlPattern = primaryPattern,
                timeout = 2000L,
            )
            extractVrfFromUrls(vrfUrls)
        }
        primaryOutcome.value?.let { return it }
        lastError = primaryOutcome.error ?: lastError

        val fallbackOutcome = retryUntilNotNull {
            val fallbackUrls = context.captureWebViewUrls(
                pageUrl = chapterUrl,
                urlPattern = fallbackPattern,
                timeout = 1000L,
            )
            extractVrfFromUrls(fallbackUrls)
        }
        fallbackOutcome.value?.let { return it }
        lastError = fallbackOutcome.error ?: lastError

        val message = "Unable to extract chapter images VRF for chapter $chapterId from chapter page: https://$domain/read/$mangaId/$langCode/$type-$chapterNumberStr"
        lastError?.let { throw Exception(message, it) }
        throw Exception(message)
    }

    /**
     * Extract VRF token for search from the main page using webview injection
     * Pattern: /ajax/manga/search?keyword=xxx&vrf=xxx
     */
    private suspend fun extractSearchVrf(keyword: String): String {
        val kw = keyword.replace("'", "\\'")
        var lastError: Throwable? = null

        val primaryOutcome = retryUntilNotNull<String>(
            attempts = 3,
            delayMs = 1000L
        ) {
            val pageJs = """
            (function(){
              console.log('[MF_VRF] PageScript started for keyword: ${kw}');
              const kw='${kw}';
              function trigger(){
                const input=document.querySelector('.search-inner input[name=keyword]');
                const form=document.querySelector('.search-inner form');
                const hiddenVrf = document.querySelector('.search-inner input[name=vrf]');
                console.log('[MF_VRF] Elements found:', {input: !!input, form: !!form, hiddenVrf: !!hiddenVrf});
                if(!input){
                  console.log('[MF_VRF] Search input not found');
                  return false;
                }
                console.log('[MF_VRF] Setting keyword and triggering search:', kw);
                input.value=kw;
                input.focus();
                input.dispatchEvent(new Event('input',{bubbles:true}));
                input.dispatchEvent(new Event('change',{bubbles:true}));
                input.dispatchEvent(new KeyboardEvent('keydown',{key:'Enter',keyCode:13,which:13,bubbles:true,cancelable:true}));
                setTimeout(()=>{
                  try{
                    if (hiddenVrf) console.log('[MF_VRF] Hidden VRF value:', hiddenVrf.value);
                    if (form) {
                      console.log('[MF_VRF] Submitting form');
                      form.submit();
                    } else {
                      console.log('[MF_VRF] No form to submit');
                    }
                  }catch(e){
                    console.log('[MF_VRF] Form submit error:', e);
                  }
                },300);
                return true;
              }
              if(!trigger()){
                console.log('[MF_VRF] Initial trigger failed, retrying...');
                const t=setInterval(()=>{
                  if(trigger()){
                    console.log('[MF_VRF] Retry successful');
                    clearInterval(t);
                  }
                },150);
                setTimeout(()=>{
                  console.log('[MF_VRF] Giving up after 5 seconds');
                  clearInterval(t);
                },5000);
              } else {
                console.log('[MF_VRF] Initial trigger successful');
              }
            })();
            """.trimIndent()

            val filterJs = """
            return url.includes('vrf=');
            """.trimIndent()

            val config = org.koitharu.kotatsu.parsers.webview.InterceptionConfig(
                timeoutMs = 15000L,          // reasonable timeout, but will stop immediately when VRF found
                pageScript = pageJs,         // this injects and executes in the WebView
                filterScript = filterJs,     // this is only the predicate
                maxRequests = 1              // Stop after finding the first VRF match!
            )

            val intercepted = context.interceptWebViewRequests(
                url = "https://${domain}/",
                config = config
            )

            // Extract VRF from filter page URL and validate it's the right pattern
            intercepted.firstNotNullOfOrNull { request ->
                val url = request.url
                println("[MF_VRF] Checking captured URL: $url")

                if (url.contains("/filter") && url.contains("keyword=") && url.contains("vrf=")) {
                    println("[MF_VRF] Found matching filter URL: $url")
                    val vrf = request.getQueryParameter("vrf")
                    if (vrf?.isNotBlank() == true) {
                        println("[MF_VRF] Extracted VRF: $vrf")
                        // Validate we can construct the search AJAX URL
                        val searchUrl = "https://${domain}/ajax/manga/search?keyword=${kw.urlEncoded()}&vrf=$vrf"
                        println("[MF_VRF] Will use AJAX URL: $searchUrl")
                        vrf
                    } else {
                        println("[MF_VRF] VRF is blank or null")
                        null
                    }
                } else {
                    println("[MF_VRF] URL doesn't match filter pattern: $url")
                    null
                }
            }
        }

        primaryOutcome.value?.let { return it }
        lastError = primaryOutcome.error ?: lastError

        val message = "Unable to extract search VRF for keyword: $keyword from page: https://$domain/"
        lastError?.let { throw Exception(message, it) }
        throw Exception(message)
    }

    /**
     * Extract VRF token for individual volume images from the actual volume page
     * Pattern: /ajax/read/volume/{volumeId}?vrf=xxx
     */
    private suspend fun extractVolumeImagesVrf(volumeId: String, mangaId: String, type: String, langCode: String, volumeNumber: Float): String {
        val volumeNumberStr = if (volumeNumber == volumeNumber.toInt().toFloat()) {
            volumeNumber.toInt().toString()
        } else {
            volumeNumber.toString()
        }
        val volumeUrl = "https://$domain/read/$mangaId/$langCode/$type-$volumeNumberStr"

        val primaryPattern = Regex("/ajax/read/volume/$volumeId\\?vrf=([^&]+)")
        val fallbackPattern = Regex("/ajax/read/volume/\\d+\\?vrf=([^&]+)")
        var lastError: Throwable? = null

        val primaryOutcome = retryUntilNotNull {
            val vrfUrls = context.captureWebViewUrls(
                pageUrl = volumeUrl,
                urlPattern = primaryPattern,
                timeout = 2000L,
            )
            extractVrfFromUrls(vrfUrls)
        }
        primaryOutcome.value?.let { return it }
        lastError = primaryOutcome.error ?: lastError

        val fallbackOutcome = retryUntilNotNull {
            val fallbackUrls = context.captureWebViewUrls(
                pageUrl = volumeUrl,
                urlPattern = fallbackPattern,
                timeout = 1000L,
            )
            extractVrfFromUrls(fallbackUrls)
        }
        fallbackOutcome.value?.let { return it }
        lastError = fallbackOutcome.error ?: lastError

        val message = "Unable to extract volume images VRF for volume $volumeId from volume page: https://$domain/read/$mangaId/$langCode/$type-$volumeNumberStr"
        lastError?.let { throw Exception(message, it) }
        throw Exception(message)
    }

    /**
     * Extract VRF token based on operation type
     * Routes to appropriate specific VRF extraction method
     */
    private suspend fun extractVrfToken(
        operation: String,
        mangaId: String? = null,
        type: String? = null,
        langCode: String? = null,
        chapterId: String? = null,
        volumeId: String? = null,
        number: Float? = null
    ): String {
        return when (operation) {
            "chapter_list" -> {
                require(mangaId != null && type != null && langCode != null) {
                    "mangaId, type, and langCode are required for chapter_list operation"
                }
                val vrf = extractChapterListVrf(mangaId, type, langCode)
                vrf
            }
            "chapter_images" -> {
                throw IllegalStateException("chapter_images VRF should be extracted directly via extractChapterImagesVrf(), not through extractVrfToken()")
            }
            "volume_images" -> {
                throw IllegalStateException("volume_images VRF should be extracted directly via extractVolumeImagesVrf(), not through extractVrfToken()")
            }
            "search" -> {
                throw IllegalStateException("search VRF should be extracted directly via extractSearchVrf(), not through extractVrfToken()")
            }
            else -> {
                throw IllegalArgumentException("Unknown VRF operation: $operation")
            }
        }
    }

    override suspend fun getListPage(page: Int, order: SortOrder, filter: MangaListFilter): List<Manga> {
        val url = "https://$domain/filter".toHttpUrl().newBuilder().apply {
            addQueryParameter("page", page.toString())
            addQueryParameter("language[]", siteLang)

            when {
                !filter.query.isNullOrEmpty() -> {
                    // Search functionality - extract VRF from filter page navigation
                    val searchVrf = extractSearchVrf(filter.query)

                    // Use the extracted VRF to make the actual AJAX search request
                    val searchResponse = client.httpGet(
                        "https://$domain/ajax/manga/search?keyword=${filter.query.urlEncoded()}&vrf=$searchVrf"
                    ).parseJson()

                    // Parse search results from JSON response
                    val resultObj = searchResponse.getJSONObject("result")
                    val htmlContent = resultObj.getString("html")
                    println("[MF_VRF] Search result count: ${resultObj.getInt("count")}")
                    println("[MF_VRF] Processing search results HTML...")

                    return htmlContent
                        .let(Jsoup::parseBodyFragment)
                        .parseSearchResults()
                }

                else -> {
                    filter.tagsExclude.forEach { tag ->
                        addQueryParameter("genre[]", "-${tag.key}")
                    }
                    filter.tags.forEach { tag ->
                        addQueryParameter("genre[]", tag.key)
                    }
                    filter.locale?.let {
                        addQueryParameter("language[]", it.language)
                    }
                    filter.states.forEach { state ->
                        addQueryParameter(
                            name = "status[]",
                            value = when (state) {
                                MangaState.ONGOING -> "releasing"
                                MangaState.FINISHED -> "completed"
                                MangaState.ABANDONED -> "discontinued"
                                MangaState.PAUSED -> "on_hiatus"
                                MangaState.UPCOMING -> "info"
                                else -> throw IllegalArgumentException("$state not supported")
                            },
                        )
                    }
                    addQueryParameter(
                        name = "sort",
                        value = when (order) {
                            SortOrder.UPDATED -> "recently_updated"
                            SortOrder.POPULARITY -> "total_views"
                            SortOrder.RATING -> "mal_score"
                            SortOrder.NEWEST -> "release_date"
                            SortOrder.ALPHABETICAL -> "title_az"
                            SortOrder.RELEVANCE -> "most_relevance"
                            else -> ""
                        },
                    )
                }
            }
        }.build()

        return client.httpGet(url)
            .parseHtml().parseMangaList()
    }

    private fun Document.parseMangaList(): List<Manga> {
        return select(".original.card-lg .unit .inner").map {
            val a = it.selectFirstOrThrow(".info > a")
            val mangaUrl = a.attrAsRelativeUrl("href")
            Manga(
                id = generateUid(mangaUrl),
                url = mangaUrl,
                publicUrl = mangaUrl.toAbsoluteUrl(domain),
                title = a.ownText(),
                coverUrl = it.selectFirstOrThrow("img").attrAsAbsoluteUrl("src"),
                source = source,
                altTitles = emptySet(),
                largeCoverUrl = null,
                authors = emptySet(),
                contentRating = null,
                rating = RATING_UNKNOWN,
                state = null,
                tags = emptySet(),
            )
        }
    }

    private fun Document.parseSearchResults(): List<Manga> {
        return select(".original.card-sm.body a.unit").map { a ->
            val mangaUrl = a.attrAsRelativeUrl("href")
            val title = a.selectFirstOrThrow(".info > h6").ownText()
            val coverUrl = a.selectFirstOrThrow(".poster img").attr("src").replace("@100", "")

            println("[MF_VRF] Parsing search result: title='$title' url='$mangaUrl' cover='$coverUrl'")

            Manga(
                id = generateUid(mangaUrl),
                url = mangaUrl,
                publicUrl = mangaUrl.toAbsoluteUrl(domain),
                title = title,
                coverUrl = coverUrl,
                source = source,
                altTitles = emptySet(),
                largeCoverUrl = null,
                authors = emptySet(),
                contentRating = null,
                rating = RATING_UNKNOWN,
                state = null,
                tags = emptySet(),
            )
        }
    }

    override suspend fun getDetails(manga: Manga): Manga {
        val document = webClient.httpGet(manga.url.toAbsoluteUrl(domain)).parseHtml()
        val availableTags = tags.get()
        var isAdult = false
        var isSuggestive = false
        val author = document.select("div.meta a[href*=/author/]")
            .joinToString { it.ownText() }.nullIfEmpty()

        return manga.copy(
            title = document.selectFirstOrThrow(".info > h1").ownText(),
            altTitles = setOfNotNull(document.selectFirst(".info > h6")?.ownTextOrNull()),
            rating = document.selectFirst("div.rating-box")?.attr("data-score")
                ?.toFloatOrNull()?.div(10) ?: RATING_UNKNOWN,
            coverUrl = document.selectFirstOrThrow("div.manga-detail div.poster img")
                .attrAsAbsoluteUrl("src"),
            tags = document.select("div.meta a[href*=/genre/]").mapNotNullToSet {
                val tag = it.ownText()
                if (tag == "Hentai") {
                    isAdult = true
                } else if (tag == "Ecchi") {
                    isSuggestive = true
                }
                availableTags[tag.toTitleCase(sourceLocale)]
            },
            contentRating = when {
                isAdult -> ContentRating.ADULT
                isSuggestive -> ContentRating.SUGGESTIVE
                else -> ContentRating.SAFE
            },
            state = document.selectFirst(".info > p")?.ownText()?.let {
                when (it.lowercase()) {
                    "releasing" -> MangaState.ONGOING
                    "completed" -> MangaState.FINISHED
                    "discontinued" -> MangaState.ABANDONED
                    "on_hiatus" -> MangaState.PAUSED
                    "info" -> MangaState.UPCOMING
                    else -> null
                }
            },
            authors = setOfNotNull(author),
            description = document.selectFirstOrThrow("#synopsis div.modal-content").html(),
            chapters = getChapters(manga.url, document),
        )
    }

    private data class ChapterBranch(
        val type: String,
        val langCode: String,
        val langTitle: String,
    )

    private suspend fun getChapters(mangaUrl: String, document: Document): List<MangaChapter> {
        val availableTypes = document.select(".chapvol-tab > a").map {
            it.attr("data-name")
        }
        val langTypePairs = document.select(".m-list div.tab-content").flatMap {
            val type = it.attr("data-name")

            it.select(".list-menu .dropdown-item").map { item ->
                ChapterBranch(
                    type = type,
                    langCode = item.attr("data-code").lowercase(),
                    langTitle = item.attr("data-title"),
                )
            }
        }.filter {
            it.langCode == siteLang && availableTypes.contains(it.type)
        }

        // Extract full manga identifier from URL (e.g., "kkochi-samkin-jimseung.kx976" from "/manga/kkochi-samkin-jimseung.kx976")
        val fullMangaId = mangaUrl.substringAfterLast('/')

        return coroutineScope {
            langTypePairs.map {
                async {
                    getChaptersBranch(fullMangaId, it)
                }
            }.awaitAll().flatten()
        }
    }

    private suspend fun getChaptersBranch(mangaId: String, branch: ChapterBranch): List<MangaChapter> {
        val readVrf = extractVrfToken(
            operation = "chapter_list",
            mangaId = mangaId,
            type = branch.type,
            langCode = branch.langCode
        )

        // Use just the ID part for AJAX requests (same as the intercepted URL pattern)
        val mangaIdPart = mangaId.substringAfterLast('.')

        val response = client
            .httpGet("https://$domain/ajax/read/$mangaIdPart/${branch.type}/${branch.langCode}?vrf=$readVrf")

        val chapterElements = response.parseJson()
            .getJSONObject("result")
            .getString("html")
            .let(Jsoup::parseBodyFragment)
            .select("ul li a")

        if (branch.type == "chapter" || branch.type == "volume") {
            val doc = client
                .httpGet("https://$domain/ajax/manga/$mangaIdPart/${branch.type}/${branch.langCode}")
                .parseJson()
                .getString("result")
                .let(Jsoup::parseBodyFragment)

            doc.select("ul li a").withIndex().forEach { (i, it) ->
                val date = it.select("span").getOrNull(1)?.ownText() ?: ""
                chapterElements[i].attr("upload-date", date)
                chapterElements[i].attr("other-title", it.attr("title"))
            }
        }

        return chapterElements.mapChapters(reversed = true) { _, it ->
            val chapterId = it.attr("data-id")
            MangaChapter(
                id = generateUid(it.attr("href")),
                title = it.attr("title").ifBlank {
                    "${branch.type.toTitleCase()} ${it.attr("data-number")}"
                },
                number = it.attr("data-number").toFloatOrNull() ?: -1f,
                volume = it.attr("other-title").let { title ->
                    volumeNumRegex.find(title)?.groupValues?.getOrNull(2)?.toInt() ?: 0
                },
                url = "$mangaId/${branch.type}/${branch.langCode}/$chapterId",
                scanlator = null,
                uploadDate = dateFormat.parseSafe(it.attr("upload-date")),
                branch = "${branch.langTitle} ${branch.type.toTitleCase()}",
                source = source,
            )
        }
    }

    private val dateFormat = SimpleDateFormat("MMM dd, yyyy", Locale.ENGLISH)
    private val volumeNumRegex = Regex("""vol(ume)?\s*(\d+)""", RegexOption.IGNORE_CASE)

    override suspend fun getRelatedManga(seed: Manga): List<Manga> = coroutineScope {
        val document = client.httpGet(seed.url.toAbsoluteUrl(domain)).parseHtml()
        val total = document.select(
            "section.m-related a[href*=/manga/], .side-manga:not(:has(.head:contains(trending))) .unit",
        ).size
        val mangas = ArrayList<Manga>(total)

        // "Related Manga"
        document.select("section.m-related a[href*=/manga/]").map {
            async {
                val url = it.attrAsRelativeUrl("href")

                val mangaDocument = client
                    .httpGet(url.toAbsoluteUrl(domain))
                    .parseHtml()

                val chaptersInManga = mangaDocument.select(".m-list div.tab-content .list-menu .dropdown-item")
                    .map { i -> i.attr("data-code").lowercase() }


                if (!chaptersInManga.contains(siteLang)) {
                    return@async null
                }

                Manga(
                    id = generateUid(url),
                    url = url,
                    publicUrl = url.toAbsoluteUrl(domain),
                    title = it.ownText(),
                    coverUrl = mangaDocument.selectFirstOrThrow("div.manga-detail div.poster img")
                        .attrAsAbsoluteUrl("src"),
                    source = source,
                    altTitles = emptySet(),
                    largeCoverUrl = null,
                    authors = emptySet(),
                    contentRating = null,
                    rating = RATING_UNKNOWN,
                    state = null,
                    tags = emptySet(),
                )
            }
        }.awaitAll()
            .filterNotNullTo(mangas)

        // "You may also like"
        document.select(".side-manga:not(:has(.head:contains(trending))) .unit").forEach {
            val url = it.attrAsRelativeUrl("href")
            mangas.add(
                Manga(
                    id = generateUid(url),
                    url = url,
                    publicUrl = url.toAbsoluteUrl(domain),
                    title = it.selectFirstOrThrow(".info h6").ownText(),
                    coverUrl = it.selectFirstOrThrow(".poster img").attrAsAbsoluteUrl("src"),
                    source = source,
                    altTitles = emptySet(),
                    largeCoverUrl = null,
                    authors = emptySet(),
                    contentRating = null,
                    rating = RATING_UNKNOWN,
                    state = null,
                    tags = emptySet(),
                ),
            )
        }

        mangas.ifEmpty {
            // fallback: author's other works
            document.select("div.meta a[href*=/author/]").map {
                async {
                    val url = it.attrAsAbsoluteUrl("href").toHttpUrl()
                        .newBuilder()
                        .addQueryParameter("language[]", siteLang)
                        .build()

                    client.httpGet(url)
                        .parseHtml().parseMangaList()
                }
            }.awaitAll().flatten()
        }
    }

    override suspend fun getPages(chapter: MangaChapter): List<MangaPage> {
        val itemId = chapter.url.substringAfterLast('/')
        // Extract mangaId from chapter URL pattern: mangaId/type/lang/itemId (itemId = chapterId or volumeId)
        val urlParts = chapter.url.split('/')
        require(urlParts.size >= 4) { "Invalid chapter URL format: ${chapter.url}" }

        val mangaId = urlParts[0]
        val type = urlParts[1]
        val langCode = urlParts[2]

        val (vrf, endpoint) = when (type) {
            "chapter" -> {
                val vrf = extractChapterImagesVrf(
                    chapterId = itemId,
                    mangaId = mangaId,
                    type = type,
                    langCode = langCode,
                    chapterNumber = chapter.number
                )
                vrf to "chapter"
            }
            "volume" -> {
                val vrf = extractVolumeImagesVrf(
                    volumeId = itemId,
                    mangaId = mangaId,
                    type = type,
                    langCode = langCode,
                    volumeNumber = chapter.number
                )
                vrf to "volume"
            }
            else -> throw IllegalArgumentException("Unknown content type: $type")
        }

        val images = client
            .httpGet("https://$domain/ajax/read/$endpoint/$itemId?vrf=$vrf")
            .parseJson()
            .getJSONObject("result")
            .getJSONArray("images")

        val pages = ArrayList<MangaPage>(images.length())

        for (i in 0 until images.length()) {
            val img = images.getJSONArray(i)

            val url = img.getString(0)
            val offset = img.getInt(2)

            pages.add(
                MangaPage(
                    id = generateUid(url),
                    url = if (offset < 1) {
                        url
                    } else {
                        "$url#scrambled_$offset"
                    },
                    preview = null,
                    source = source,
                ),
            )
        }

        return pages
    }

    private fun Int.ceilDiv(other: Int) = (this + (other - 1)) / other

    @MangaSourceParser("MANGAFIRE_EN", "MangaFire English", "en")
    class English(context: MangaLoaderContext) : MangaFireParser(context, MangaParserSource.MANGAFIRE_EN, "en")

    @MangaSourceParser("MANGAFIRE_ES", "MangaFire Spanish", "es")
    class Spanish(context: MangaLoaderContext) : MangaFireParser(context, MangaParserSource.MANGAFIRE_ES, "es")

    @MangaSourceParser("MANGAFIRE_ESLA", "MangaFire Spanish (Latim)", "es")
    class SpanishLatim(context: MangaLoaderContext) :
        MangaFireParser(context, MangaParserSource.MANGAFIRE_ESLA, "es-la")

    @MangaSourceParser("MANGAFIRE_FR", "MangaFire French", "fr")
    class French(context: MangaLoaderContext) : MangaFireParser(context, MangaParserSource.MANGAFIRE_FR, "fr")

    @MangaSourceParser("MANGAFIRE_JA", "MangaFire Japanese", "ja")
    class Japanese(context: MangaLoaderContext) : MangaFireParser(context, MangaParserSource.MANGAFIRE_JA, "ja")

    @MangaSourceParser("MANGAFIRE_PT", "MangaFire Portuguese", "pt")
    class Portuguese(context: MangaLoaderContext) : MangaFireParser(context, MangaParserSource.MANGAFIRE_PT, "pt")

    @MangaSourceParser("MANGAFIRE_PTBR", "MangaFire Portuguese (Brazil)", "pt")
    class PortugueseBR(context: MangaLoaderContext) :
        MangaFireParser(context, MangaParserSource.MANGAFIRE_PTBR, "pt-br")
}

public object SSLUtils {
    public val trustAllCerts: Array<TrustManager> = arrayOf(@Suppress("CustomX509TrustManager")
    object : X509TrustManager {
        override fun getAcceptedIssuers(): Array<X509Certificate> = emptyArray()
        override fun checkClientTrusted(certs: Array<X509Certificate>, authType: String) = Unit
        override fun checkServerTrusted(certs: Array<X509Certificate>, authType: String) = Unit
    })

    public val sslSocketFactory: SSLSocketFactory? = SSLContext.getInstance("SSL").apply {
        init(null, trustAllCerts, SecureRandom())
    }.socketFactory

    public val trustManager: X509TrustManager = trustAllCerts[0] as X509TrustManager
}
