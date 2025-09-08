- The linter is now controled through the command-line argument `-linting-level n`;
  level 0 disables linting; default level is 1 (issues reported at that level must
  be fixed); command-line argument `-wall` enables linting level 2 (also reports
  less severe issues)
  ([PR 1275](https://github.com/jasmin-lang/jasmin/pull/1275)).
