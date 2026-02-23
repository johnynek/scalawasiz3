package dev.bosatsu.scalawasiz3

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

  def decodeAndDecompressLz4(base64Chunks: Array[String], uncompressedSize: Int): Option[Array[Byte]] =
    try {
      val compressed = decodeBase64Chunks(base64Chunks)
      Some(SimpleLZ4.decompress(compressed, uncompressedSize))
    } catch {
      case _: Throwable => None
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
}
