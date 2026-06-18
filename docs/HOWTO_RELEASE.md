How to release
==============

## Automated release

Most of the release is automated by the [Stainless Release](../.github/workflows/stainless-release.yml)
GitHub Actions workflow.

1. Update [RELEASE\_NOTES.md](RELEASE_NOTES.md) and merge it to the release branch (usually `main`).
2. Run the **Stainless Release** workflow manually (Actions tab → *Stainless Release* → *Run workflow*),
   from the branch you want to release, and provide the version (e.g. `v0.9.9.4`).

The workflow then automatically:

- bumps the version in the Sphinx docs ([core/src/sphinx/conf.py](../core/src/sphinx/conf.py));
- commits that bump and creates an annotated `vX.X.X` tag on it, then pushes both;
- builds the standalone archives with `./bin/package-standalone.sh` and the SBT plugin
  archive with `./bin/package-sbt-plugin.sh`;
- creates the GitHub release with auto-generated notes and the archives attached
  (without renaming them).

Note: the tag is annotated but **not** GPG-signed (the manual process below used
`git tag -s`); signing in CI would require importing a GPG key from a repository secret.

[//]: # (TODO: Release the Docker image with `./bin/docker-release.sh VERSION`, where `VERSION` is of the form `X.X.X` &#40;without a leading `v`&#41;.)

## Manual release

If you need to release by hand:

1. Update [RELEASE\_NOTES.md](RELEASE_NOTES.md).
2. Make sure that the  Git working copy is not dirty, ie. that `git diff --stat` does not output anything.
3. Tag the release with `git tag -a -s VERSION`, where `VERSION` is of the form `vX.X.X`.
   In the tag commit message, include the release notes for that version.
4. Push the tag to GitHub with `git push --tags`.
5. Build the standalone archives for macOS and Linux with `./bin/package-standalone.sh`.
6. Build the SBT plugin archive for all platform with `./bin/package-sbt-plugin.sh`. 
7. Create a new release on GitHub, add the release notes for that version and attach the archives. Make sure to not rename the archives.

## Notes

#### Versioning

[`sbt-git`](https://github.com/sbt/sbt-git) is used to automatically create a unique version.
In short, if the current commit is tagged, then the tag will be used.
Otherwise, the git hash of the last commit is appended to the set project's version.
If the working copy is "dirty", then `-SNAPSHOT` will be added to the version string.

The advantage of doing this is that you have a stable version number for each commit,
making it trivial for people to correlate a release with a commit in the project.

