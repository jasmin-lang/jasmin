# Unreleased changelog

## Description

This directory contains the pieces of changelog describing the unreleased changes to Jasmin.
Each change is described in its own file.
The files will be merged into [`CHANGELOG.md`](../CHANGELOG.md) when the changes make it to a release.
This avoids having conflicts between PRs just because of additions to the changelog.

## Describing your change

- Pick one of the existing directories depending on the kind of change you implemented.
- Create a file `<PR number>-some-title.md` in the corresponding directory.
- Describe your change in a concise manner, and mention the fixed issue if applicable.
  For instance:
  ```
  - This is a precise but short description of the change that I wrote
    ([PR #<PR number>](https://github.com/jasmin-lang/jasmin/pull/<PR number>);
    fixes [#<issue number>](https://github.com/jasmin-lang/jasmin/issues/<issue number>)).
  ```

## Generating the unreleased changelog

If you prepare the next release, or just want to get a synthetic view of the unreleased changes,
just run from the root of the repository:

```
./scripts/generate-release-changelog.sh
```
