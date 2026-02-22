package dev.bosatsu.scalawasiz3

class JsEmbeddedBytesSuite extends munit.FunSuite {
  test("embedded wasm bytes are generated") {
    assert(EmbeddedWasmBytes.wasm.nonEmpty)
  }
}
