package dev.bosatsu.scalawasiz3

import scala.scalanative.unsafe.*

private[scalawasiz3] object Z3NativeApiConstants {
  val Z3_OK: CInt = 0
}

@link("z3")
@extern
private[scalawasiz3] object Z3NativeApi {
  type Z3_config = Ptr[Byte]
  type Z3_context = Ptr[Byte]
  type Z3_string = CString
  type Z3_error_code = CInt
  type Z3_error_handler = CFuncPtr2[Z3_context, Z3_error_code, Unit]

  def Z3_mk_config(): Z3_config = extern
  def Z3_set_param_value(c: Z3_config, paramId: Z3_string, paramValue: Z3_string): Unit = extern
  def Z3_mk_context(c: Z3_config): Z3_context = extern
  def Z3_del_context(c: Z3_context): Unit = extern
  def Z3_del_config(c: Z3_config): Unit = extern
  def Z3_eval_smtlib2_string(c: Z3_context, str: Z3_string): Z3_string = extern
  def Z3_get_error_code(c: Z3_context): Z3_error_code = extern
  def Z3_get_error_msg(c: Z3_context, err: Z3_error_code): Z3_string = extern
  def Z3_set_error_handler(c: Z3_context, h: Z3_error_handler): Unit = extern
}
