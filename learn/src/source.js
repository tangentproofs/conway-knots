// Line-range highlighting for the source pages: #L9 or #L9-L28. Click a line number to select it,
// shift-click to extend. The range bar names the declaration and links to its node page and GitHub.
(function () {
  "use strict";
  var S = window.SRC || {}, anchor = null;
  var hdr = document.querySelector("header.top");
  function setHdr() { var st = hdr && getComputedStyle(hdr).position === "sticky"; document.documentElement.style.setProperty("--hdr", (st ? hdr.offsetHeight : 0) + "px"); }
  setHdr(); addEventListener("resize", setHdr);
  if (window.matchMedia("(max-width: 800px)").matches) {
    var f = document.querySelector(".src-files"); if (f && S.file) f.open = false;
  }
  function parse(h) {
    var m = /^#L(\d+)(?:-L(\d+))?$/.exec(h || "");
    if (!m) return null;
    var a = +m[1], b = m[2] ? +m[2] : a;
    return a <= b ? [a, b] : [b, a];
  }
  function esc(s) { return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;"); }
  function apply(scroll) {
    document.querySelectorAll(".sl.hl").forEach(function (e) { e.classList.remove("hl", "hl-first", "hl-last"); });
    document.querySelectorAll(".src-outline li.on").forEach(function (e) { e.classList.remove("on"); });
    var bar = document.getElementById("range"), gh = document.getElementById("gh");
    var r = parse(location.hash);
    if (!r) { if (bar) bar.hidden = true; if (gh) gh.href = S.github; return; }
    for (var i = r[0]; i <= r[1]; i++) {
      var el = document.getElementById("L" + i);
      if (!el) continue;
      el.classList.add("hl");
      if (i === r[0]) el.classList.add("hl-first");
      if (i === r[1]) el.classList.add("hl-last");
    }
    var frag = "#L" + r[0] + (r[1] !== r[0] ? "-L" + r[1] : "");
    if (gh) gh.href = S.github + frag;
    var d = null;
    (S.decls || []).forEach(function (x) { if (!d && x[1] === r[0] && x[2] === r[1]) d = x; });
    if (!d) (S.decls || []).forEach(function (x) { if (!d && x[1] <= r[0] && r[1] <= x[2]) d = x; });
    document.querySelectorAll('.src-outline a[href="#L' + (d ? d[1] + (d[2] !== d[1] ? "-L" + d[2] : "") : "") + '"]').forEach(function (a) { a.parentNode.classList.add("on"); });
    if (bar) {
      var nm = S.file.split("/").pop();
      bar.innerHTML = "<span><b>" + (r[1] !== r[0] ? "Lines " + r[0] + "\u2013" + r[1] : "Line " + r[0]) + "</b> of <code>" + esc(nm) + "</code></span>" +
        (d ? "<span>" + (d[1] === r[0] && d[2] === r[1] ? "" : "in ") + "<code>" + esc(d[0]) + "</code></span>" +
          (d[3] ? '<a href="' + esc(S.root + "index.html#/node/" + encodeURIComponent(d[3])) + '">' + (d[4] ? "\u00b6 plain English" : "\u00b6 node page") + "</a>" : "") : "") +
        '<span class="grow"></span><a class="small" href="' + esc(S.github + frag) + '" target="_blank" rel="noopener">these lines on GitHub \u2197</a>' +
        '<button type="button" id="clear" title="Clear the highlight">\u00d7</button>';
      bar.hidden = false;
      document.getElementById("clear").onclick = function () { history.replaceState(null, "", location.pathname + location.search); anchor = null; apply(false); };
    }
    if (scroll) {
      var first = document.getElementById("L" + r[0]);
      if (first) first.scrollIntoView({ block: r[1] - r[0] > 25 ? "start" : "center" });
    }
  }
  document.addEventListener("click", function (ev) {
    var a = ev.target.closest && ev.target.closest(".sl > a.n");
    if (!a) return;
    ev.preventDefault();
    var n = +a.dataset.n, cur = parse(location.hash);
    var h = (ev.shiftKey && (anchor || (cur && cur[0]))) ? "#L" + Math.min(anchor || cur[0], n) + "-L" + Math.max(anchor || cur[0], n) : "#L" + n;
    if (!ev.shiftKey) anchor = n;
    history.replaceState(null, "", h);
    apply(false);
  });
  addEventListener("hashchange", function () { apply(true); });
  apply(true);
})();
