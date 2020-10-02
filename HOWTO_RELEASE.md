How to release
==============

## Prepare release

1. Update [RELEASE\_NOTES.md](RELEASE_NOTES.md).
2. Make sure that the  Git working copy is not dirty, ie. that `git diff --stat` does not output anything.
3. Tag the release with `git tag -a -s VERSION`, where `VERSION` is of the form `vX.X.X`.
   In the tag commit message, include the release notes for that version.
4. Push the tag to GitHub with `git push --tags`.
5. Build the standalone archives for macOS and Linux with `./bin/package-standalone.sh`.
6. Create a new release on GitHub, add the release notes for that version and attach the two archives. Make sure to not rename the archives.
7. Release the Docker image with `./bin/docker-release.sh VERSION`, where `VERSION` is of the form `X.X.X` (without a leading `v`).

## Publish to Bintray

### Precondition

1. You need to be part of the [epfl-lara bintray organization](https://bintray.com/epfl-lara) (ask Nicolas Voirol - [@samarion](https://github.com/samarion) - if you need to be added to the organization).
2. You have created a `.credentials` file under the `~/.bintray` folder, e.g.,

```
$ cat .bintray/.credentials 
realm = Bintray API Realm
host = api.bintray.com
user = <your-bintray-username>
password = <your-bintray-api-token>
```

Read the [bintray documentation](https://bintray.com/docs/usermanual/interacting/interacting_interacting.html#anchorAPIKEY) for how to obtain an API token.

### Publishing

To cut a release simply execute `sbt publish`. All artifacts are going to be published under https://bintray.com/epfl-lara.

## Notes

#### Versioning

[`sbt-git`](https://github.com/sbt/sbt-git) is used to automatically create a unique version.
In short, if the current commit is tagged, then the tag will be used.
Otherwise, the git hash of the last commit is appended to the set project's version.
If the working copy is "dirty", then `-SNAPSHOT` will be added to the version string.

The advantage of doing this is that you have a stable version number for each commit,
making it trivial for people to correlate a release with a commit in the project.

