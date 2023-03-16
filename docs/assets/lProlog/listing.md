---
title: λProlog to DAMF Bridge -- Files
---
<div id="listing"></div>
<script>
  const ghUser = "distributed-assertions";
  const ghRepo = "distributed-assertions.github.io";
  const ghPath = "/assets/lProlog";
  const ghRef  = "gh-pages";
  const ghApiUrl = `https://api.github.com/repos/${ ghUser }/${ ghRepo }/contents${ ghPath }?ref=${ ghRef }`;
  (async () => {
    const response = await fetch(ghApiUrl);
    const data = await response.json();
    let contents = "<ul>";
    for (let file of data) {
       if (file.name.endsWith(".md")) continue;
       contents += `<li><a href="${ file.download_url }">${ file.name }</a></li>`;
    }
    document.getElementById("listing").innerHTML = contents;
  })();
</script>
