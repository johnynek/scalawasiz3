import org.scalajs.linker.interface.ModuleKind
import sbtcrossproject.CrossPlugin.autoImport.{CrossType, crossProject}
import java.io.BufferedWriter
import java.io.FileOutputStream
import java.io.OutputStreamWriter
import java.nio.charset.StandardCharsets
import java.util.Base64

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
          val encoder = Base64.getEncoder

          writer.write("package dev.bosatsu.scalawasiz3\n\n")
          writer.write("private[scalawasiz3] object EmbeddedWasmBytes {\n")
          writer.write("  private val base64Chunks: Array[String] = Array(\n")

          var first = true
          val chunkIter = bytes.grouped(chunkSize)
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
            """  private val decodeTable: Array[Int] = {
              |    val table = Array.fill(256)(-1)
              |    val alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
              |    var i = 0
              |    while (i < alphabet.length) {
              |      table(alphabet.charAt(i).toInt) = i
              |      i += 1
              |    }
              |    table('='.toInt) = 0
              |    table
              |  }
              |
              |  private def decodeChunk(chunk: String): Array[Byte] = {
              |    val len = chunk.length
              |    var padding = 0
              |    if (len >= 1 && chunk.charAt(len - 1) == '=') padding += 1
              |    if (len >= 2 && chunk.charAt(len - 2) == '=') padding += 1
              |    val out = new Array[Byte](((len * 3) / 4) - padding)
              |
              |    var inPos = 0
              |    var outPos = 0
              |    while (inPos < len) {
              |      val c0 = decodeTable(chunk.charAt(inPos).toInt)
              |      val c1 = decodeTable(chunk.charAt(inPos + 1).toInt)
              |      val c2 = decodeTable(chunk.charAt(inPos + 2).toInt)
              |      val c3 = decodeTable(chunk.charAt(inPos + 3).toInt)
              |      val bits = (c0 << 18) | (c1 << 12) | (c2 << 6) | c3
              |
              |      out(outPos) = ((bits >>> 16) & 0xff).toByte
              |      outPos += 1
              |      if (outPos < out.length) {
              |        out(outPos) = ((bits >>> 8) & 0xff).toByte
              |        outPos += 1
              |      }
              |      if (outPos < out.length) {
              |        out(outPos) = (bits & 0xff).toByte
              |        outPos += 1
              |      }
              |
              |      inPos += 4
              |    }
              |
              |    out
              |  }
              |
              |  lazy val wasm: Array[Byte] = {
              |    val decodedChunks = new Array[Array[Byte]](base64Chunks.length)
              |    var total = 0
              |    var idx = 0
              |    while (idx < base64Chunks.length) {
              |      val decoded = decodeChunk(base64Chunks(idx))
              |      decodedChunks(idx) = decoded
              |      total += decoded.length
              |      idx += 1
              |    }
              |
              |    val out = new Array[Byte](total)
              |    var pos = 0
              |    idx = 0
              |    while (idx < decodedChunks.length) {
              |      val chunk = decodedChunks(idx)
              |      java.lang.System.arraycopy(chunk, 0, out, pos, chunk.length)
              |      pos += chunk.length
              |      idx += 1
              |    }
              |    out
              |  }
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
