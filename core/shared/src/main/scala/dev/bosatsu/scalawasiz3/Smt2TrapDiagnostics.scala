package dev.bosatsu.scalawasiz3

import scala.collection.mutable.ArrayBuffer

private[scalawasiz3] object Smt2TrapDiagnostics {

  final case class SyntheticError(message: String, stdout: String)

  private sealed trait TokenKind
  private case object LParen extends TokenKind
  private case object RParen extends TokenKind
  private case object Atom extends TokenKind

  private final case class Token(kind: TokenKind, text: String, line: Int, column: Int)
  private final case class DepthToken(token: Token, depth: Int)
  private final case class Command(name: String, withDepth: Vector[DepthToken])
  private final case class Diagnostic(line: Int, column: Int, body: String) {
    def message: String = s"line $line column $column: $body"
  }

  private val BuiltinSorts: Set[String] = Set(
    "Bool",
    "Int",
    "Real",
    "String",
    "RegLan",
    "RoundingMode"
  )

  private val BuiltinTerms: Set[String] = Set(
    "true",
    "false",
    "and",
    "or",
    "not",
    "=>",
    "xor",
    "ite",
    "let",
    "forall",
    "exists",
    "lambda",
    "par",
    "as",
    "_",
    "!",
    "match",
    "=",
    "distinct",
    "+",
    "-",
    "*",
    "/",
    "div",
    "mod",
    "abs",
    "to_real",
    "to_int",
    "is_int",
    "<",
    "<=",
    ">",
    ">=",
    "check-sat",
    "assert",
    "set-logic",
    "set-option",
    "set-info",
    "declare-const",
    "declare-fun",
    "declare-sort",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "declare-datatype",
    "declare-datatypes"
  )

  def isUnreachableTrapMessage(message: String): Boolean =
    Option(message).exists(_.toLowerCase.contains("unreachable"))

  def fromInput(input: String): Option[SyntheticError] = {
    val tokens = tokenize(input)

    findParenthesisDiagnostic(tokens, input)
      .orElse(inferTypeDiagnostic(tokens))
      .map(toSyntheticError)
  }

  private def toSyntheticError(d: Diagnostic): SyntheticError = {
    val msg = d.message
    val escaped = escapeForSmt(msg)
    SyntheticError(message = msg, stdout = s"(error \"$escaped\")\n")
  }

  private def findParenthesisDiagnostic(tokens: Vector[Token], input: String): Option[Diagnostic] = {
    val stack = ArrayBuffer.empty[Token]
    var idx = 0
    while (idx < tokens.length) {
      tokens(idx).kind match {
        case LParen =>
          stack += tokens(idx)
        case RParen =>
          if (stack.isEmpty) {
            val t = tokens(idx)
            return Some(Diagnostic(t.line, t.column, "invalid expression, unexpected ')'"))
          }
          stack.remove(stack.length - 1)
        case Atom =>
          ()
      }
      idx += 1
    }

    if (stack.nonEmpty) {
      val (line, column) = eofPosition(input)
      Some(Diagnostic(line, column, "invalid expression, unexpected end of file"))
    } else None
  }

  private def inferTypeDiagnostic(tokens: Vector[Token]): Option[Diagnostic] = {
    val commands = extractTopLevelCommands(tokens)
    var declaredSymbols = Set.empty[String]
    var declaredSorts = BuiltinSorts

    var idx = 0
    while (idx < commands.length) {
      val command = commands(idx)
      command.name match {
        case "declare-sort" =>
          atomsAtDepth(command, depth = 1).lift(1).foreach { sortTok =>
            declaredSorts += sortTok.text
          }

        case "declare-const" =>
          atomsAtDepth(command, depth = 1).lift(1).foreach { symbolTok =>
            declaredSymbols += symbolTok.text
          }

          atomsAtDepth(command, depth = 1).lift(2).flatMap { sortTok =>
            unknownSimpleSort(sortTok, declaredSorts)
          } match {
            case Some(diag) => return Some(diag)
            case None       => ()
          }

        case "declare-fun" =>
          atomsAtDepth(command, depth = 1).lift(1).foreach { symbolTok =>
            declaredSymbols += symbolTok.text
          }

          atomsAtDepth(command, depth = 1).lift(2).flatMap { sortTok =>
            unknownSimpleSort(sortTok, declaredSorts)
          } match {
            case Some(diag) => return Some(diag)
            case None       => ()
          }

        case "define-fun" | "define-fun-rec" =>
          atomsAtDepth(command, depth = 1).lift(1).foreach { symbolTok =>
            declaredSymbols += symbolTok.text
          }

        case "assert" =>
          findUnknownSymbol(command, declaredSymbols) match {
            case Some(diag) => return Some(diag)
            case None       => ()
          }

        case _ =>
          ()
      }

      idx += 1
    }

    None
  }

  private def unknownSimpleSort(sortTok: Token, declaredSorts: Set[String]): Option[Diagnostic] =
    if (isIdentifierLike(sortTok.text) && !declaredSorts.contains(sortTok.text)) {
      Some(Diagnostic(sortTok.line, sortTok.column, s"unknown sort '${sortTok.text}'"))
    } else None

  private def findUnknownSymbol(command: Command, declaredSymbols: Set[String]): Option[Diagnostic] = {
    val atoms = command.withDepth.collect {
      case DepthToken(token, depth) if token.kind == Atom && depth >= 1 => token
    }

    atoms.drop(1).find { token =>
      val text = token.text
      isIdentifierLike(text) &&
      !declaredSymbols.contains(text) &&
      !BuiltinTerms.contains(text) &&
      !BuiltinSorts.contains(text) &&
      !text.startsWith(":") &&
      !text.startsWith("#") &&
      !isNumeral(text)
    }.map { unknown =>
      Diagnostic(unknown.line, unknown.column, s"unknown constant/variable '${unknown.text}'")
    }
  }

  private def atomsAtDepth(command: Command, depth: Int): Vector[Token] =
    command.withDepth.collect {
      case DepthToken(token, d) if d == depth && token.kind == Atom => token
    }

  private def extractTopLevelCommands(tokens: Vector[Token]): Vector[Command] = {
    val out = Vector.newBuilder[Command]
    var idx = 0

    while (idx < tokens.length) {
      tokens(idx).kind match {
        case LParen =>
          val start = idx
          var depth = 1
          idx += 1

          while (idx < tokens.length && depth > 0) {
            tokens(idx).kind match {
              case LParen => depth += 1
              case RParen => depth -= 1
              case Atom   => ()
            }
            idx += 1
          }

          if (depth == 0) {
            val slice = tokens.slice(start, idx)
            val depthTokens = withDepth(slice)
            depthTokens.collectFirst {
              case DepthToken(token, d) if d == 1 && token.kind == Atom => token.text
            }.foreach { name =>
              out += Command(name = name, withDepth = depthTokens)
            }
          }

        case RParen | Atom =>
          idx += 1
      }
    }

    out.result()
  }

  private def withDepth(tokens: Vector[Token]): Vector[DepthToken] = {
    val out = Vector.newBuilder[DepthToken]
    var depth = 0

    var idx = 0
    while (idx < tokens.length) {
      val token = tokens(idx)
      token.kind match {
        case LParen =>
          depth += 1
          out += DepthToken(token, depth)

        case RParen =>
          out += DepthToken(token, depth)
          depth -= 1

        case Atom =>
          out += DepthToken(token, depth)
      }

      idx += 1
    }

    out.result()
  }

  private def tokenize(input: String): Vector[Token] = {
    val out = Vector.newBuilder[Token]

    var idx = 0
    var line = 1
    var column = 1

    def consumeChar(): Char = {
      val ch = input.charAt(idx)
      idx += 1
      if (ch == '\n') {
        line += 1
        column = 1
      } else {
        column += 1
      }
      ch
    }

    def isDelimiter(ch: Char): Boolean =
      ch.isWhitespace || ch == '(' || ch == ')' || ch == ';'

    def consumeStringToken(): Unit = {
      val startLine = line
      val startCol = column
      val sb = new StringBuilder
      sb.append(consumeChar())

      var done = false
      while (idx < input.length && !done) {
        val ch = consumeChar()
        sb.append(ch)
        if (ch == '"') {
          if (idx < input.length && input.charAt(idx) == '"') {
            sb.append(consumeChar())
          } else {
            done = true
          }
        }
      }

      out += Token(Atom, sb.result(), startLine, startCol)
    }

    def consumeQuotedSymbolToken(): Unit = {
      val startLine = line
      val startCol = column
      val sb = new StringBuilder
      sb.append(consumeChar())

      var escaped = false
      var done = false
      while (idx < input.length && !done) {
        val ch = consumeChar()
        sb.append(ch)
        if (escaped) {
          escaped = false
        } else if (ch == '\\') {
          escaped = true
        } else if (ch == '|') {
          done = true
        }
      }

      out += Token(Atom, sb.result(), startLine, startCol)
    }

    def consumeAtomToken(): Unit = {
      val startLine = line
      val startCol = column
      val sb = new StringBuilder
      while (idx < input.length && !isDelimiter(input.charAt(idx))) {
        sb.append(consumeChar())
      }
      if (sb.nonEmpty) {
        out += Token(Atom, sb.result(), startLine, startCol)
      }
    }

    while (idx < input.length) {
      val ch = input.charAt(idx)
      if (ch.isWhitespace) {
        consumeChar()
      } else if (ch == ';') {
        while (idx < input.length && input.charAt(idx) != '\n') {
          consumeChar()
        }
      } else if (ch == '(') {
        out += Token(LParen, "(", line, column)
        consumeChar()
      } else if (ch == ')') {
        out += Token(RParen, ")", line, column)
        consumeChar()
      } else if (ch == '"') {
        consumeStringToken()
      } else if (ch == '|') {
        consumeQuotedSymbolToken()
      } else {
        consumeAtomToken()
      }
    }

    out.result()
  }

  private def eofPosition(input: String): (Int, Int) = {
    var line = 1
    var column = 1
    var idx = 0

    while (idx < input.length) {
      val ch = input.charAt(idx)
      if (ch == '\n') {
        line += 1
        column = 1
      } else {
        column += 1
      }
      idx += 1
    }

    (line, column)
  }

  private def isNumeral(text: String): Boolean =
    text.nonEmpty && text.forall(ch => ch.isDigit || ch == '.' || ch == '-')

  private def isIdentifierLike(text: String): Boolean = {
    if (text.isEmpty) false
    else {
      val first = text.charAt(0)
      first.isLetter || first == '_' || first == '|'
    }
  }

  private def escapeForSmt(value: String): String =
    value
      .replace("\\", "\\\\")
      .replace("\"", "\\\"")
}
