How to release
==============

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

### Releasing

To cut a release simply execute `sbt publish`. All artifacts are going to be published under https://bintray.com/epfl-lara.

#### Versioning

[`sbt-git`](https://github.com/sbt/sbt-git) is used to automatically create a unique version. In short, the git hash of the last commit is appended to the set project's version. The advantage of doing this is that you have a stable version number for each commit, making it trivial for people to correlate a release with a commit in the project.

