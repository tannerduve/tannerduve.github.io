// Wait for both MathJax and page to be ready before initializing TikzJax
document.addEventListener('DOMContentLoaded', function() {
  const tikzScripts = document.querySelectorAll('script[type="text/tikz"]');
  
  if (tikzScripts.length > 0) {
    // Wrap all TikZ script tags in a container div for proper layout
    tikzScripts.forEach(function(script) {
      const wrapper = document.createElement('div');
      wrapper.className = 'tikz-container';
      script.parentNode.insertBefore(wrapper, script);
      wrapper.appendChild(script);
    });
    
    // Load TikzJax and fix SVG positioning after it renders
    const tikzScript = document.createElement('script');
    tikzScript.src = 'https://tikzjax.com/v1/tikzjax.js';
    tikzScript.onload = function() {
      // After TikzJax processes, fix any absolutely positioned SVGs
      setTimeout(function() {
        document.querySelectorAll('.tikz-container svg').forEach(function(svg) {
          svg.style.position = 'relative';
          svg.style.display = 'block';
          svg.style.margin = '0 auto';
        });
      }, 500);
    };
    document.body.appendChild(tikzScript);
  }
});

