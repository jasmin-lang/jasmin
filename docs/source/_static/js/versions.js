// This file is a modified version of https://github.com/readthedocs/sphinx_rtd_theme/blob/5a263753d52c1628c88392fbf52c729f5a8e79b5/sphinx_rtd_theme/static/js/versions.js_t
// Changes:
// - no duplication between stable and the current stable tag
// - changing version preserves the current path in the doc

/*
The MIT License (MIT)

Copyright (c) 2013-2018 Dave Snider, Read the Docs, Inc. & contributors

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

function onSelectorSwitch(event) {
  const option = event.target.selectedIndex;
  const item = event.target.options[option];
  window.location.href = item.dataset.url;
}

document.addEventListener("readthedocs-addons-data-ready", function (event) {
  const config = event.detail.data();

  const versionSwitch = document.querySelector(
    "div.switch-menus > div.version-switch",
  );

  let versions = config.versions.active;

  // HACK: It is assumed that index 0 is latest, 1 is stable and 2 is the current stable tag.
  // We rename stable with the current stable tag + we remove the stable tag.
  stable_tag = versions[2].verbose_name
  versions[1].verbose_name = stable_tag + " (stable)";
  versions.splice(2,1);

  if (config.versions.current.hidden || config.versions.current.type === "external") {
    versions.unshift(config.versions.current);
  }
  const versionSelect = `
    <select>
      ${versions
        .map(
          (version) => `
        <option
  value="${version.slug}"
  ${config.versions.current.slug === version.slug ? 'selected="selected"' : ""}
  ${config.versions.current.slug === stable_tag && version.slug == "stable" ? 'selected="selected"' : ""}
              data-url="${window.location.pathname.replace(config.versions.current.slug, version.slug)}">
              ${version.verbose_name}
          </option>`,
        )
        .join("\n")}
    </select>
  `;

  versionSwitch.innerHTML = versionSelect;
  versionSwitch.firstElementChild.addEventListener("change", onSelectorSwitch);
});

document.addEventListener("readthedocs-addons-data-ready", function (event) {
  // Trigger the Read the Docs Addons Search modal when clicking on "Search docs" input from the topnav.
  document
    .querySelector("[role='search'] input")
    .addEventListener("focusin", () => {
      const event = new CustomEvent("readthedocs-search-show");
      document.dispatchEvent(event);
    });
});

