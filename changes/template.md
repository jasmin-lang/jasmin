{{ "# " ~ versiondata.name ~ " " ~ versiondata.version ~ " — " ~ versiondata.date }}

{% for section, section_body in sections.items() %}
{% for category, val in definitions.items() if category in section_body %}
{{ "## " ~ definitions[category]['name'] ~ "\n" }}
{% for text, _ in section_body[category].items() %}
{{ "- " ~ text }}

{% endfor %}
{% endfor %}
{% endfor %}
