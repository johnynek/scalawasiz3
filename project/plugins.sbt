import scala.io.Source

def readVersion(key: String): String = {
  val versionsFile = file("versions.properties")
  val src = Source.fromFile(versionsFile, "UTF-8")
  try {
    src.getLines().collectFirst {
      case line if line.startsWith(s"$key=") => line.substring(key.length + 1).trim
    }.getOrElse(sys.error(s"missing $key in ${versionsFile.getAbsolutePath}"))
  } finally src.close()
}

val scalaNativeVersion = readVersion("scala.native.version")
val crossProjectVersion = "1.3.2"

addSbtPlugin("org.scala-js" % "sbt-scalajs" % "1.20.1")
addSbtPlugin("org.scala-native" % "sbt-scala-native" % scalaNativeVersion)
addSbtPlugin("org.portable-scala" % "sbt-scalajs-crossproject" % crossProjectVersion)
addSbtPlugin("org.portable-scala" % "sbt-scala-native-crossproject" % crossProjectVersion)
addSbtPlugin("com.github.sbt" % "sbt-ci-release" % "1.11.2")
addSbtPlugin("org.scalameta" % "sbt-native-image" % "0.3.4")

libraryDependencies += "org.lz4" % "lz4-java" % "1.8.0"
libraryDependencies += "com.dylibso.chicory" % "build-time-compiler" % "1.7.2"
