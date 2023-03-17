export async function populateListing(params) {
  const url = `https://api.github.com/repos/${ params.user }/${ params.repo }/contents${ params.path }?ref=${ params.ref }`;
  const response = await fetch(url);
  const data = await response.json();
  let fileList = "<ul>";
  for (let file of data) {
     if (file.type !== "file") continue;
     if (file.name.endsWith(".md")) continue;
     fileList += `<li><a href="${ file.download_url }">${ file.name }</a></li>`;
  }
  const listing = document.getElementById(params.id);
  listing.classList.add("collapsible");
  const header = document.createElement("div");
  header.classList.add("collapsible-header");
  const contents = document.createElement("div");
  contents.classList.add("collapsible-content");
  header.innerHTML = "(click to expand)";
  contents.innerHTML = fileList;
  header.addEventListener("click", (ev) => {
    if (contents.style.maxHeight) {
      header.innerHTML = "(click to expand)";
      contents.style.maxHeight = null;
    } else {
      header.innerHTML = "(click to collapse)";
      contents.style.maxHeight = `${ contents.scrollHeight }px`;
    }
    ev.stopPropagation();
    return false;
  });
  listing.appendChild(header);
  listing.appendChild(contents);
  // header.dispatchEvent(new Event("click"));
}
