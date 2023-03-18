import { Octokit } from "https://cdn.skypack.dev/octokit";

const octokit = new Octokit();

const humanSuffixes = ['B', 'KiB', 'MiB', 'GiB', 'TiB'];
function humanizeSize(count) {
  const step = 1024;
  let i = count === 0 ? 0 : Math.floor(Math.log(count) / Math.log(step));
  return (count / Math.pow(step, i)).toFixed(2) * 1 + ' ' + humanSuffixes[i];
}

export async function populateListing(params) {
  const listing = document.getElementById(params.id);
  listing.classList.add("collapsible");
  listing.innerHTML = "Loading...";
  const data = await octokit.rest.repos.getContent({
    owner: params.user,
    repo: params.repo,
    path: params.path,
    ref: params.ref
  }).then((response) => {
    listing.innerHTML = "";
    return response.data;
  }).catch((error) => {
    listing.innerHTML = `<span style="color:red;font-weight:bold;">Loading failed... HTTP ${ error.status }</span>`;
  });
  if (!data) return; // failure
  let accept = undefined;
  if (params.accept) {
    if (params.accept instanceof RegExp)
      accept = (name) => name.match(params.accept);
    else if (params.accept instanceof Array)
      accept = (name) => params.accept.includes(name);
  }
  let reject = undefined;
  if (params.reject) {
    if (params.reject instanceof RegExp)
      reject = (name) => name.match(params.reject);
    else if (params.reject instanceof Array)
      reject = (name) => params.reject.includes(name);
  }
  const fileList = [];
  for (const file of data) {
    if (file.type !== "file") continue;
    if (accept && !accept(file.name)) continue;
    if (reject && reject(file.name)) continue;
    fileList.push(file);
  }
  const count = fileList.length;
  const expandMsg = `<strong>${ count } files</strong> (click to expand)`;
  const collapseMsg = `<strong>${ count } files</strong> (click to collapse)`;
  let fileListRendered = "<ul>";
  for (const file of fileList)
    fileListRendered += `<li><a href="${ file.download_url }">${ file.name }</a> <span class="faded">(${ humanizeSize(file.size) })</span></li>`;
  fileListRendered += "</ul>";
  if (params.collapsible) {
    const header = document.createElement("div");
    header.classList.add("collapsible-header");
    const contents = document.createElement("div");
    contents.classList.add("collapsible-content");
    header.innerHTML = expandMsg;
    contents.innerHTML = fileListRendered;
    header.addEventListener("click", (ev) => {
      if (contents.style.maxHeight) {
        header.innerHTML = expandMsg;
        contents.style.maxHeight = null;
      } else {
        header.innerHTML = collapseMsg;
        contents.style.maxHeight = `${contents.scrollHeight}px`;
      }
      ev.stopPropagation();
      return false;
    });
    listing.appendChild(header);
    listing.appendChild(contents);
    // contents.style.maxHeight = `${contents.scrollHeight}px`;
  } else {
    listing.classList.add("collapsible");
    listing.innerHTML = fileListRendered;
  }
}
