package dev.bosatsu.scalawasiz3

import scala.scalajs.js
import scala.scalajs.js.typedarray.Uint8Array

private[scalawasiz3] object EmbeddedWasmSupport {
  private val decodeTable: Array[Int] = {
    val table = Array.fill(256)(-1)
    val alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    var i = 0
    while (i < alphabet.length) {
      table(alphabet.charAt(i).toInt) = i
      i += 1
    }
    table('='.toInt) = 0
    table
  }

  def decodeAndGunzip(base64Chunks: Array[String]): Option[Array[Byte]] = {
    val compressed = decodeBase64Chunks(base64Chunks)
    gunzipOnNode(compressed)
  }

  private def decodeBase64Chunks(base64Chunks: Array[String]): Array[Byte] = {
    val decodedChunks = new Array[Array[Byte]](base64Chunks.length)
    var total = 0
    var idx = 0
    while (idx < base64Chunks.length) {
      val decoded = decodeChunk(base64Chunks(idx))
      decodedChunks(idx) = decoded
      total += decoded.length
      idx += 1
    }

    val out = new Array[Byte](total)
    var pos = 0
    idx = 0
    while (idx < decodedChunks.length) {
      val chunk = decodedChunks(idx)
      java.lang.System.arraycopy(chunk, 0, out, pos, chunk.length)
      pos += chunk.length
      idx += 1
    }
    out
  }

  private def decodeChunk(chunk: String): Array[Byte] = {
    val len = chunk.length
    var padding = 0
    if (len >= 1 && chunk.charAt(len - 1) == '=') padding += 1
    if (len >= 2 && chunk.charAt(len - 2) == '=') padding += 1
    val out = new Array[Byte](((len * 3) / 4) - padding)

    var inPos = 0
    var outPos = 0
    while (inPos < len) {
      val c0 = decodeTable(chunk.charAt(inPos).toInt)
      val c1 = decodeTable(chunk.charAt(inPos + 1).toInt)
      val c2 = decodeTable(chunk.charAt(inPos + 2).toInt)
      val c3 = decodeTable(chunk.charAt(inPos + 3).toInt)
      val bits = (c0 << 18) | (c1 << 12) | (c2 << 6) | c3

      out(outPos) = ((bits >>> 16) & 0xff).toByte
      outPos += 1
      if (outPos < out.length) {
        out(outPos) = ((bits >>> 8) & 0xff).toByte
        outPos += 1
      }
      if (outPos < out.length) {
        out(outPos) = (bits & 0xff).toByte
        outPos += 1
      }

      inPos += 4
    }

    out
  }

  private def gunzipOnNode(compressed: Array[Byte]): Option[Array[Byte]] = {
    val zlib =
      loadNodeModule("node:zlib")
        .orElse(loadNodeModule("zlib"))
    zlib.flatMap { module =>
      val gunzipSync = module.selectDynamic("gunzipSync")
      if (js.isUndefined(gunzipSync) || gunzipSync == null) None
      else {
        try {
          val out = gunzipSync
            .asInstanceOf[js.Function1[js.Any, js.Any]]
            .apply(toUint8Array(compressed))
          Some(toByteArray(out.asInstanceOf[Uint8Array]))
        } catch {
          case _: Throwable => None
        }
      }
    }
  }

  private def loadNodeModule(name: String): Option[js.Dynamic] = {
    val fromBuiltin = globalProcess().flatMap { process =>
      val getBuiltinModule = process.selectDynamic("getBuiltinModule")
      if (!js.isUndefined(getBuiltinModule) && getBuiltinModule != null) {
        try {
          val module = getBuiltinModule.asInstanceOf[js.Function1[String, js.Any]].apply(name)
          if (!js.isUndefined(module) && module != null) {
            Some(module.asInstanceOf[js.Dynamic])
          } else {
            None
          }
        } catch {
          case _: Throwable => None
        }
      } else {
        None
      }
    }

    fromBuiltin.orElse {
      globalRequire() match {
        case None => None
        case Some(requireFn) =>
          try {
            val module = requireFn.asInstanceOf[js.Function1[String, js.Any]].apply(name)
            if (js.isUndefined(module) || module == null) None
            else Some(module.asInstanceOf[js.Dynamic])
          } catch {
            case _: Throwable => None
          }
      }
    }
  }

  private def toUint8Array(bytes: Array[Byte]): Uint8Array = {
    val out = new Uint8Array(bytes.length)
    var i = 0
    while (i < bytes.length) {
      out(i) = (bytes(i).toInt & 0xff).toShort
      i += 1
    }
    out
  }

  private def toByteArray(bytes: Uint8Array): Array[Byte] = {
    val out = new Array[Byte](bytes.length)
    var i = 0
    while (i < bytes.length) {
      out(i) = bytes(i).toByte
      i += 1
    }
    out
  }

  private def globalProcess(): Option[js.Dynamic] =
    fromGlobalThis(_.selectDynamic("process"))
      .orElse {
        try asDefined(js.Dynamic.global.selectDynamic("process"))
        catch {
          case _: Throwable => None
        }
      }

  private def globalRequire(): Option[js.Dynamic] =
    fromGlobalThis(_.selectDynamic("require"))
      .orElse {
        try asDefined(js.Dynamic.global.selectDynamic("require"))
        catch {
          case _: Throwable => None
        }
      }

  private def fromGlobalThis(read: js.Dynamic => js.Any): Option[js.Dynamic] = {
    try {
      val globalThis = js.Dynamic.global.selectDynamic("globalThis")
      if (js.isUndefined(globalThis) || globalThis == null) None
      else asDefined(read(globalThis.asInstanceOf[js.Dynamic]))
    } catch {
      case _: Throwable => None
    }
  }

  private def asDefined(value: js.Any): Option[js.Dynamic] =
    if (js.isUndefined(value) || value == null) None else Some(value.asInstanceOf[js.Dynamic])
}
