# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = "Jasmin"
copyright = "Jasmin contributors"
author = "The Jasmin developer team"

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = ["myst_parser", "sphinx_rtd_theme", "sphinx.ext.graphviz"]

myst_enable_extensions = ["colon_fence"]
myst_heading_anchors = 3

graphviz_output_format = "svg"

highlight_language = 'none'

# templates_path = ['_templates']
# exclude_patterns = []


# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = "sphinx_rtd_theme"
html_theme_options = {"sticky_navigation": False}
html_context = {
    "display_github": True,  # Integrate GitHub
    "github_user": "jasmin-lang",  # Username
    "github_repo": "jasmin",  # Repo name
    "github_version": "main",  # Version
    "conf_py_path": "/docs/source/",  # Path in the checkout to the docs root
    'versions': [
        ("dev", "https://rocq-prover.org/doc/master/refman/"),
        ("stable", "https://rocq-prover.org/refman/"),
        ("9.1", "https://rocq-prover.org/doc/v9.1/refman/"),
        ("9.0", "https://rocq-prover.org/doc/v9.0/refman/"),
        ("8.20", "https://rocq-prover.org/doc/V8.20.1/refman/"),
        ("8.19", "https://rocq-prover.org/doc/V8.19.2/refman/"),
        ("8.18", "https://rocq-prover.org/doc/V8.18.0/refman/"),
        ("8.17", "https://rocq-prover.org/doc/V8.17.1/refman/"),
        ("8.16", "https://rocq-prover.org/doc/V8.16.1/refman/"),
        ("8.15", "https://rocq-prover.org/doc/V8.15.2/refman/"),
        ("8.14", "https://rocq-prover.org/doc/V8.14.1/refman/"),
        ("8.13", "https://rocq-prover.org/doc/V8.13.2/refman/"),
        ("8.12", "https://rocq-prover.org/doc/V8.12.2/refman/"),
        ("8.11", "https://rocq-prover.org/doc/V8.11.2/refman/"),
        ("8.10", "https://rocq-prover.org/doc/V8.10.2/refman/"),
        ("8.9", "https://rocq-prover.org/doc/V8.9.1/refman/"),
        ("8.8", "https://rocq-prover.org/doc/V8.8.2/refman/"),
        ("8.7", "https://rocq-prover.org/doc/V8.7.2/refman/"),
        ("8.6", "https://rocq-prover.org/doc/V8.6.1/refman/"),
        ("8.5", "https://rocq-prover.org/doc/V8.5pl3/refman/"),
        ("8.4", "https://rocq-prover.org/doc/V8.4pl6/refman/"),
        ("8.3", "https://rocq-prover.org/doc/V8.3pl5/refman/"),
        ("8.2", "https://rocq-prover.org/doc/V8.2pl3/refman/"),
        ("8.1", "https://rocq-prover.org/doc/V8.1pl6/refman/"),
        ("8.0", "https://rocq-prover.org/doc/V8.0/doc/")
}
# html_static_path = ['_static']
