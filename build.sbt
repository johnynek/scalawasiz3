import org.scalajs.linker.interface.ModuleKind
import sbtcrossproject.CrossPlugin.autoImport.{CrossType, crossProject}

val chicoryVersion = "1.4.0"
val munitVersion = "1.1.1"

ThisBuild / organization := "dev.bosatsu"
ThisBuild / scalaVersion := "3.8.1"
ThisBuild / versionScheme := Some("early-semver")
ThisBuild / licenses := List("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0"))
ThisBuild / homepage := Some(url("https://github.com/bosatsu/dev.bosatsu.scalawasiz3"))
ThisBuild / scmInfo := Some(
  ScmInfo(
    url("https://github.com/bosatsu/dev.bosatsu.scalawasiz3"),
    "scm:git@github.com:bosatsu/dev.bosatsu.scalawasiz3.git"
  )
)
ThisBuild / developers := List(
  Developer(
    id = "bosatsu",
    name = "Bosatsu",
    email = "",
    url = url("https://github.com/bosatsu")
  )
)

ThisBuild / Test / fork := false

lazy val root = project
  .in(file("."))
  .aggregate(core.jvm, core.js)
  .settings(
    name := "scalawasiz3-root",
    moduleName := "scalawasiz3-root",
    publish / skip := true
  )

lazy val core =
  crossProject(JSPlatform, JVMPlatform)
    .crossType(CrossType.Full)
    .in(file("core"))
    .settings(
      name := "scalawasiz3",
      moduleName := "scalawasiz3",
      libraryDependencies += "org.scalameta" %%% "munit" % munitVersion % Test
    )
    .jvmSettings(
      libraryDependencies ++= Seq(
        "com.dylibso.chicory" % "runtime" % chicoryVersion,
        "com.dylibso.chicory" % "wasm" % chicoryVersion,
        "com.dylibso.chicory" % "wasi" % chicoryVersion
      )
    )
    .jsSettings(
      scalaJSLinkerConfig ~= { _.withModuleKind(ModuleKind.ESModule) },
      Compile / sourceGenerators += Def.task {
        val log = streams.value.log
        val wasmFile = (LocalRootProject / baseDirectory).value / "core" / "shared" / "src" / "main" / "resources" / "dev" / "bosatsu" / "scalawasiz3" / "z3" / "z3.wasm"
        val outDir = (Compile / sourceManaged).value / "dev" / "bosatsu" / "scalawasiz3"
        val outFile = outDir / "EmbeddedWasmBytes.scala"
        val chunkSize = 16 * 1024

        val generated = if (wasmFile.exists()) {
          val bytes = IO.readBytes(wasmFile)
          val chunkStrings =
            bytes
              .grouped(chunkSize)
              .map(chunk => s"    Array[Byte](${chunk.map(_.toString).mkString(", ")})")
              .mkString(",\n")

          s"""package dev.bosatsu.scalawasiz3
              |
              |private[scalawasiz3] object EmbeddedWasmBytes {
              |  private val chunked: Array[Array[Byte]] = Array(
              |$chunkStrings
              |  )
              |
              |  lazy val wasm: Array[Byte] = {
              |    val total = chunked.foldLeft(0)(_ + _.length)
              |    val out = new Array[Byte](total)
              |    var pos = 0
              |    var idx = 0
              |    while (idx < chunked.length) {
              |      val c = chunked(idx)
              |      java.lang.System.arraycopy(c, 0, out, pos, c.length)
              |      pos += c.length
              |      idx += 1
              |    }
              |    out
              |  }
              |}
              |""".stripMargin
        } else {
          log.warn(s"WASM resource not found at ${wasmFile.getAbsolutePath}; generating empty placeholder bytes for Scala.js compile")
          s"""package dev.bosatsu.scalawasiz3
              |
              |private[scalawasiz3] object EmbeddedWasmBytes {
              |  lazy val wasm: Array[Byte] = Array.emptyByteArray
              |}
              |""".stripMargin
        }

        IO.write(outFile, generated)
        Seq(outFile)
      }.taskValue
    )

lazy val coreJVM = core.jvm
lazy val coreJS = core.js
