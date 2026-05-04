<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
                xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:atom="http://www.w3.org/2005/Atom"
                exclude-result-prefixes="atom">
  <xsl:output method="html" encoding="UTF-8" indent="yes"
              doctype-system="about:legacy-compat"/>

  <xsl:template match="/atom:feed">
    <html lang="en">
      <head>
        <title><xsl:value-of select="atom:title"/> — RSS Feed</title>
        <meta charset="UTF-8"/>
        <meta name="viewport" content="width=device-width, initial-scale=1"/>
        <style>
          :root {
            --bg: #ffffff;
            --fg: #1c1c1d;
            --muted: #6e6e73;
            --accent: #b509ac;
            --border: rgba(0,0,0,0.1);
            --card-bg: #faf7fb;
          }
          @media (prefers-color-scheme: dark) {
            :root {
              --bg: #1c1c1d;
              --fg: #e8e8e8;
              --muted: #9e9ea3;
              --accent: #d77fcf;
              --border: rgba(255,255,255,0.12);
              --card-bg: #232325;
            }
          }
          * { box-sizing: border-box; }
          body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            background: var(--bg);
            color: var(--fg);
            margin: 0;
            padding: 2rem 1rem;
            line-height: 1.55;
          }
          .container { max-width: 720px; margin: 0 auto; }
          header { margin-bottom: 2.5rem; padding-bottom: 1.5rem; border-bottom: 1px solid var(--border); }
          header h1 { margin: 0 0 0.5rem 0; font-size: 1.75rem; }
          header .subtitle { margin: 0; color: var(--muted); font-size: 0.95rem; }
          .rss-info {
            margin: 1.5rem 0 0;
            padding: 1rem 1.25rem;
            background: var(--card-bg);
            border: 1px solid var(--border);
            border-radius: 8px;
            font-size: 0.9rem;
            color: var(--muted);
          }
          .rss-info strong { color: var(--fg); }
          .rss-info code {
            background: var(--bg);
            padding: 0.1rem 0.35rem;
            border-radius: 4px;
            border: 1px solid var(--border);
            font-size: 0.85em;
          }
          article {
            padding: 1.25rem 0;
            border-bottom: 1px solid var(--border);
          }
          article:last-child { border-bottom: none; }
          article h2 { margin: 0 0 0.35rem 0; font-size: 1.15rem; font-weight: 600; line-height: 1.3; }
          article h2 a { color: var(--accent); text-decoration: none; }
          article h2 a:hover { text-decoration: underline; }
          article time { display: block; color: var(--muted); font-size: 0.8rem; margin-bottom: 0.6rem; letter-spacing: 0.02em; }
          article .summary { margin: 0; color: var(--fg); font-size: 0.95rem; }
        </style>
      </head>
      <body>
        <div class="container">
          <header>
            <h1><xsl:value-of select="atom:title"/></h1>
            <p class="subtitle">RSS feed</p>
            <div class="rss-info">
              <p style="margin:0 0 0.5rem 0;"><strong>This is a feed, not a webpage.</strong></p>
              <p style="margin:0;">
                Paste this URL into a feed reader (e.g. Feedly, NetNewsWire, Inoreader)
                to get notified when new posts go up:
                <code>
                  <xsl:value-of select="atom:link[@rel='self']/@href"/>
                </code>
              </p>
            </div>
          </header>

          <main>
            <xsl:for-each select="atom:entry">
              <article>
                <h2>
                  <a>
                    <xsl:attribute name="href">
                      <xsl:value-of select="atom:link/@href"/>
                    </xsl:attribute>
                    <xsl:value-of select="atom:title"/>
                  </a>
                </h2>
                <time>
                  <xsl:value-of select="substring(atom:published, 1, 10)"/>
                </time>
                <p class="summary">
                  <xsl:value-of select="atom:summary" disable-output-escaping="yes"/>
                </p>
              </article>
            </xsl:for-each>
          </main>
        </div>
      </body>
    </html>
  </xsl:template>
</xsl:stylesheet>
