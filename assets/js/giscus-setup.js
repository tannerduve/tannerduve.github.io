function determineGiscusTheme() {
  
    let theme =
      localStorage.getItem("theme") ||
      document.documentElement.getAttribute("data-theme") ||
      "system";

    if (theme === "dark") return "dark_dimmed";
    if (theme === "light") return "light";

    const prefersDark = window.matchMedia("(prefers-color-scheme: dark)").matches;
    return prefersDark ? "dark_dimmed" : "light";
  
}

(function setupGiscus() {
  let giscusTheme = determineGiscusTheme();

  let giscusAttributes = {
    src: "https://giscus.app/client.js",
    "data-repo": "tannerduve/tannerduve.github.io",
    "data-repo-id": "R_kgDOQYRz4g",
    "data-category": "Announcements",
    "data-category-id": "DIC_kwDOQYRz4s4C8LCI",
    "data-mapping": "pathname",
    "data-strict": "0",
    "data-reactions-enabled": "1",
    "data-emit-metadata": "0",
    "data-input-position": "bottom",
    "data-theme": giscusTheme,
    "data-lang": "en",
    "data-loading": "lazy",
    crossorigin: "anonymous",
    async: true,
  };

  let giscusScript = document.createElement("script");
  Object.entries(giscusAttributes).forEach(([key, value]) =>
    giscusScript.setAttribute(key, value)
  );
  document.getElementById("giscus_thread").appendChild(giscusScript);
})();

