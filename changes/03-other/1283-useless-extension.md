- Redundant zero-extensions of primitives (when the size of the extension
  is the same as the size of the primitive output) are now accepted
  instead of rejected.
  The useless zero-extension is dropped, and a warning is emitted.
  ([PR #1283](https://github.com/jasmin-lang/jasmin/pull/1283)).
