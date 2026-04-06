package dev.bosatsu.scalawasiz3

object Z3Platform {
  lazy val default: Z3Solver = NativeZ3Solver.default

  def create(): Z3Solver = NativeZ3Solver.create()
}
