The formal semantics of Jasmin is now based on interaction trees instead
of a big step semantics ([PR 1489](https://github.com/jasmin-lang/jasmin/pull/1489), [PR 1444](https://github.com/jasmin-lang/jasmin/pull/1444)).
For the user the only difference is that
 - The compiler provides strong garanties on non-terminating program
 - The safety checker does not need to ensure loop termination

