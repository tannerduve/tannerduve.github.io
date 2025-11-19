window.MathJax = {
  tex: {
    tags: "ams",
    inlineMath: [
      ["$", "$"],
      ["\\(", "\\)"],
    ],
  },
  options: {
    skipHtmlTags: ["script", "noscript", "style", "textarea", "pre", "code"],
    ignoreHtmlClass: "tex2jax_ignore",
    processHtmlClass: "tex2jax_process",
    renderActions: {
      addCss: [
        200,
        function (doc) {
          const style = document.createElement("style");
          style.innerHTML = `
          .mjx-container {
            color: inherit;
          }
        `;
          document.head.appendChild(style);
        },
        "",
      ],
    },
  },
  startup: {
    ready() {
      MathJax.startup.defaultReady();
      // Ensure MathJax doesn't process TikZ script tags
      MathJax.startup.document.skipTags = MathJax.startup.document.skipTags || [];
      if (!MathJax.startup.document.skipTags.includes('script[type="text/tikz"]')) {
        MathJax.startup.document.skipTags.push('script[type="text/tikz"]');
      }
    },
  },
};
