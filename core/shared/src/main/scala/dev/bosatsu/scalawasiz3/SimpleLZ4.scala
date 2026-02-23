package dev.bosatsu.scalawasiz3

private[scalawasiz3] object SimpleLZ4 {
  def decompress(input: Array[Byte], uncompressedSize: Int): Array[Byte] = {
    val dest = new Array[Byte](uncompressedSize)
    var ip = 0
    var op = 0

    while (ip < input.length) {
      val token = input(ip) & 0xff
      ip += 1

      var litLen = token >>> 4
      if (litLen == 15) {
        var l = 255
        while (l == 255 && ip < input.length) {
          l = input(ip) & 0xff
          ip += 1
          litLen += l
        }
      }

      if (litLen > 0) {
        java.lang.System.arraycopy(input, ip, dest, op, litLen)
        ip += litLen
        op += litLen
      }

      if (ip < input.length) {
        val offset = (input(ip) & 0xff) | ((input(ip + 1) & 0xff) << 8)
        if (offset <= 0 || offset > op) {
          throw new IllegalArgumentException(s"Invalid LZ4 offset: $offset at output position $op")
        }
        ip += 2

        var matchLen = token & 0x0f
        if (matchLen == 15) {
          var l = 255
          while (l == 255 && ip < input.length) {
            l = input(ip) & 0xff
            ip += 1
            matchLen += l
          }
        }
        matchLen += 4

        var matchPtr = op - offset
        var i = 0
        while (i < matchLen) {
          dest(op) = dest(matchPtr)
          op += 1
          matchPtr += 1
          i += 1
        }
      }
    }

    if (op != uncompressedSize) {
      throw new IllegalArgumentException(
        s"Invalid LZ4 stream: expected $uncompressedSize output bytes but wrote $op"
      )
    }
    dest
  }
}
