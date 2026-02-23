import org.scalajs.linker.interface.ModuleKind
import sbtcrossproject.CrossPlugin.autoImport.{CrossType, crossProject}
import java.io.BufferedWriter
import java.io.ByteArrayOutputStream
import java.io.FileOutputStream
import java.io.OutputStreamWriter
import java.nio.charset.StandardCharsets
import java.util.Base64
import java.util.zip.GZIPOutputStream

val chicoryVersion = "1.4.0"
val munitVersion = "1.1.1"
lazy val ensureZ3WasmResources = taskKey[Unit]("Ensure generated Z3 WASM resources exist before compilation.")

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

lazy val core =
  crossProject(JSPlatform, JVMPlatform)
    .crossType(CrossType.Full)
    .in(file("core"))
    .settings(
      name := "scalawasiz3",
      moduleName := "scalawasiz3",
      libraryDependencies += "org.scalameta" %%% "munit" % munitVersion % Test,
      ensureZ3WasmResources := {
        val resourceDir =
          (LocalRootProject / baseDirectory).value / "core" / "shared" / "src" / "main" / "resources" / "dev" / "bosatsu" / "scalawasiz3" / "z3"
        val requiredFiles = Seq(
          resourceDir / "z3.wasm",
          resourceDir / "z3.wasm.sha256"
        )
        val missing = requiredFiles.filterNot(_.exists())
        if (missing.nonEmpty) {
          val missingText = missing.map(_.getAbsolutePath).mkString("\n  - ")
          sys.error(
            s"""Missing generated Z3 WASM resources:
               |  - $missingText
               |
               |Run ./scripts/build-z3-wasi.sh and rerun sbt.
               |""".stripMargin
          )
        }
      },
      Compile / compile := (Compile / compile).dependsOn(ensureZ3WasmResources).value
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
        val wasmFile = (LocalRootProject / baseDirectory).value / "core" / "shared" / "src" / "main" / "resources" / "dev" / "bosatsu" / "scalawasiz3" / "z3" / "z3.wasm"
        val outDir = (Compile / sourceManaged).value / "dev" / "bosatsu" / "scalawasiz3"
        val outFile = outDir / "EmbeddedWasmBytes.scala"
        val chunkSize = 32 * 1024

        if (!wasmFile.exists()) {
          sys.error(
            s"""Missing required Z3 WASM resource at ${wasmFile.getAbsolutePath}
               |
               |Run ./scripts/build-z3-wasi.sh and rerun sbt.
               |""".stripMargin
          )
        }

        IO.createDirectory(outDir)
        val writer: BufferedWriter =
          new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outFile), StandardCharsets.UTF_8))

        try {
          val bytes = IO.readBytes(wasmFile)
          val gzipOut = new ByteArrayOutputStream(math.max(1024, bytes.length / 3))
          val gzip = new GZIPOutputStream(gzipOut)
          try {
            gzip.write(bytes)
          } finally {
            gzip.close()
          }
          val compressedBytes = gzipOut.toByteArray
          val encoder = Base64.getEncoder

          writer.write("package dev.bosatsu.scalawasiz3\n\n")
          writer.write("private[scalawasiz3] object EmbeddedWasmBytes {\n")
          writer.write("  private val gzippedBase64Chunks: Array[String] = Array(\n")

          var first = true
          val chunkIter = compressedBytes.grouped(chunkSize)
          while (chunkIter.hasNext) {
            val encoded = encoder.encodeToString(chunkIter.next())
            if (!first) {
              writer.write(",\n")
            }
            writer.write("    \"")
            writer.write(encoded)
            writer.write("\"")
            first = false
          }
          writer.write("\n  )\n\n")

          writer.write(
            """  lazy val wasm: Array[Byte] =
              |    EmbeddedWasmSupport.decodeAndGunzip(gzippedBase64Chunks)
              |}
              |""".stripMargin
          )
        } finally {
          writer.close()
        }

        Seq(outFile)
      }.taskValue
    )

lazy val coreJVM = core.jvm
  .enablePlugins(NativeImagePlugin)
  .settings(
    Compile / mainClass := Some("dev.bosatsu.scalawasiz3.Main"),
    nativeImageJvm := "graalvm-java17",
    nativeImageVersion := "22.3.0",
    nativeImageOptions ++= Seq(
      "--no-fallback",
      "-H:IncludeResources=dev/bosatsu/scalawasiz3/z3/.*"
    ),
    nativeImageOutput := (Compile / target).value / "native-image" / "scalawasiz3-z3-main"
  )
lazy val coreJS = core.js

lazy val root = project
  .in(file("."))
  .aggregate(coreJVM, coreJS)
  .settings(
    name := "scalawasiz3-root",
    moduleName := "scalawasiz3-root",
    publish / skip := true
  )
