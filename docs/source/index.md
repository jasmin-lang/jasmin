# The Jasmin documentation

<p id=blou>toto</p>

<script>
document.addEventListener(
  "readthedocs-addons-data-ready",
  function (event) {
    const config = event.detail.data();

    // Create the version selector HTML
    const versionSelector = `
      <div class="version-selector">
        <select onchange="window.location.href=this.value">
          <option value="${config.versions.current.urls.documentation}">
            ${config.versions.current.slug}
          </option>
          ${config.versions.active
            .filter(v => v.slug !== config.versions.current.slug)
            .map(version => `
              <option value="${version.urls.documentation}">
                ${version.slug}
              </option>
            `).join('')}
        </select>
      </div>
    `;

    // Insert the version selector into your page
    document.querySelector('#blou')
      .insertAdjacentHTML('beforeend', versionSelector);
  }
);
</script>

:::{include} about.md
:heading-offset: 1
:::

:::{toctree}
:caption: Language reference

language/syntax/index
language/semantics/index
:::

:::{toctree}
:caption: Compiler

compiler/passes/index
compiler/advanced/index
:::

:::{toctree}
:caption: Tools

tools/jasminc
tools/jasmin2ec
tools/safety_checker
tools/linter
tools/ct
tools/sct
tools/reference_interpreter
tools/jasmin2tex
:::

:::{toctree}
:caption: Miscellaneous

misc/installation_guide
misc/faq
misc/emacs_mode
:::

:::{include} bibliography.md
:heading-offset: 1
:::
