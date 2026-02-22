package dev.bosatsu.scalawasiz3

object Z3Platform {
  lazy val default: Z3Solver = JsWasiZ3Solver
}
