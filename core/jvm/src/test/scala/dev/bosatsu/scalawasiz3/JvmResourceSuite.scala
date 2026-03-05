package dev.bosatsu.scalawasiz3

class JvmResourceSuite extends munit.FunSuite {
  private val generatedModuleClassName = "dev.bosatsu.scalawasiz3.aot.Z3Module"
  private val generatedMetaWasmPath = "/dev/bosatsu/scalawasiz3/aot/Z3Module.meta"

  test("JVM build packages Chicory AOT resources") {
    val metaWasmStream = getClass.getResourceAsStream(generatedMetaWasmPath)
    assert(metaWasmStream != null)
    metaWasmStream.close()

    val generatedModuleClass = Class.forName(generatedModuleClassName)
    assert(generatedModuleClass != null)
  }

  test("JVM build does not package raw z3.wasm resource") {
    val stream = getClass.getResourceAsStream(Z3WasmResource.ClasspathResourcePath)
    assert(stream == null)
  }
}
