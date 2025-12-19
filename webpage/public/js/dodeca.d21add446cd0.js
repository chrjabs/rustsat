// Copy button for code blocks
document.addEventListener('DOMContentLoaded', function() {
    document.querySelectorAll('pre > code').forEach(function(code) {
        var pre = code.parentElement;
        if (pre.querySelector('.copy-btn')) return;
        var btn = document.createElement('button');
        btn.className = 'copy-btn';
        btn.textContent = 'Copy';
        btn.setAttribute('aria-label', 'Copy code to clipboard');
        btn.onclick = function() {
            navigator.clipboard.writeText(code.textContent).then(function() {
                btn.textContent = 'Copied!';
                btn.classList.add('copied');
                setTimeout(function() {
                    btn.textContent = 'Copy';
                    btn.classList.remove('copied');
                }, 2000);
            });
        };
        pre.appendChild(btn);
    });

    // Sidebar: mark active link and scroll into view
    var path = location.pathname;
    var links = document.querySelectorAll('.sidebar a, .sidebar-nav a, aside a');
    links.forEach(function(a) {
        if (a.pathname === path || (path.endsWith('/') && a.pathname === path.slice(0, -1))) {
            a.classList.add('active');
            var nav = a.closest('.sidebar, .sidebar-nav, aside');
            if (nav) nav.scrollTop = a.offsetTop - nav.offsetHeight / 2;
        }
    });
});
