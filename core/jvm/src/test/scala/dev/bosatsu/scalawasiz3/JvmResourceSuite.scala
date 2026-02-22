package dev.bosatsu.scalawasiz3

class JvmResourceSuite extends munit.FunSuite {
  test("z3.wasm resource is packaged") {
    val stream = getClass.getResourceAsStream(Z3WasmResource.ClasspathResourcePath)
    assert(stream != null)
    stream.close()
  }
}
