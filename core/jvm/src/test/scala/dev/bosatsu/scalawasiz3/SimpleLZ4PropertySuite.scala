package dev.bosatsu.scalawasiz3

import munit.ScalaCheckSuite
import net.jpountz.lz4.LZ4Factory
import org.scalacheck.Arbitrary
import org.scalacheck.Gen
import org.scalacheck.Prop

class SimpleLZ4PropertySuite extends ScalaCheckSuite {
  private val compressor = LZ4Factory.fastestInstance().highCompressor()

  private val byteArrayGen: Gen[Array[Byte]] =
    for {
      size <- Gen.chooseNum(0, 16 * 1024)
      bytes <- Gen.containerOfN[Array, Byte](size, Arbitrary.arbByte.arbitrary)
    } yield bytes

  property("SimpleLZ4.decompress inverts lz4-java highCompressor") {
    Prop.forAll(byteArrayGen) { input =>
      val maxCompressedLength = compressor.maxCompressedLength(input.length)
      val compressedBuffer = new Array[Byte](maxCompressedLength)
      val compressedLength =
        compressor.compress(input, 0, input.length, compressedBuffer, 0, maxCompressedLength)
      val compressed = java.util.Arrays.copyOf(compressedBuffer, compressedLength)
      val decompressed = SimpleLZ4.decompress(compressed, input.length)
      assertEquals(decompressed.toIndexedSeq, input.toIndexedSeq)
    }
  }
}
