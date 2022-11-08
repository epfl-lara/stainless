How to release
==============

## Prepare release

1. Update [RELEASE\_NOTES.md](RELEASE_NOTES.md).
2. Make sure that the  Git working copy is not dirty, ie. that `git diff --stat` does not output anything.
3. Tag the release with `git tag -a -s VERSION`, where `VERSION` is of the form `vX.X.X`.
   In the tag commit message, include the release notes for that version.
4. Push the tag to GitHub with `git push --tags`.
5. Build the standalone archives for macOS and Linux with `./bin/package-standalone.sh`.
6. Build the SBT plugin archive for all platform with `./bin/package-sbt-plugin.sh`. 
7. Create a new release on GitHub, add the release notes for that version and attach the archives. Make sure to not rename the archives.

[//]: # (7. Release the Docker image with `./bin/docker-release.sh VERSION`, where `VERSION` is of the form `X.X.X` &#40;without a leading `v`&#41;.)

## Notes

#### Versioning

[`sbt-git`](https://github.com/sbt/sbt-git) is used to automatically create a unique version.
In short, if the current commit is tagged, then the tag will be used.
Otherwise, the git hash of the last commit is appended to the set project's version.
If the working copy is "dirty", then `-SNAPSHOT` will be added to the version string.

The advantage of doing this is that you have a stable version number for each commit,
making it trivial for people to correlate a release with a commit in the project.

