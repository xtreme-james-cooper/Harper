package main

object Parser {

  def pEmpty : Parser[Unit] = new Parser(s => List(((), s)))

  def pSat(b : String => Boolean) : Parser[String] = new Parser({
    case tok :: toks if b(tok) => List((tok, toks))
    case _                     => Nil
  })

  def pLit(s : String) : Parser[String] = pSat(_ == s)

  def pIdent : Parser[String] = pSat(s => s.head.isLower || s.head == '_')

  def pNum : Parser[Int] = pSat(_.forall(_.isDigit)) map Integer.decode

  def pEnd : Parser[Unit] = new Parser({
    case tok :: toks => Nil
    case Nil         => List(((), Nil))
  })

  def tokenize(s : String) : List[String] = s.headOption match {
    case None                      => Nil
    case Some(c) if c.isWhitespace => tokenize(s.tail)
    case Some(c) if c.isDigit      => s.takeWhile(_ isDigit) :: tokenize(s.dropWhile(_ isDigit))
    case Some(c) if c.isLetter     => s.takeWhile(_ isLetterOrDigit) :: tokenize(s.dropWhile(_ isLetterOrDigit))
    case Some(c)                   => c.toString :: tokenize(s.tail)
  }

  def parse[A](s : String, parser : Parser[A]) : Option[A] = {
    def firstFullParse(ps : List[(A, List[String])]) : Option[A] = ps match {
      case Nil            => None
      case (p, Nil) :: ps => Some(p)
      case (p, x) :: ps   => firstFullParse(ps)
    }
    firstFullParse(parser.run(tokenize(s)))
  }

}

sealed class Parser[A](val run : List[String] => List[(A, List[String])]) {

  def ||(other : => Parser[A]) : Parser[A] = new Parser(s => run(s) ++ other.run(s))

  def flatMap[B](other : A => Parser[B]) : Parser[B] = new Parser(s =>
    for {
      (v1, toks) <- run(s)
      (v2, toks2) <- other(v1).run(toks)
    } yield (v2, toks2))

  def map[B](op : A => B) : Parser[B] = new Parser(s =>
    for {
      (v, toks) <- run(s)
    } yield (op(v), toks))

  def withFilter(p : A => Boolean) : Parser[A] = new Parser(s => for {
    (v, toks) <- run(s)
    if p(v)
  } yield (v, toks))

  def * : Parser[List[A]] = this.+ || (for (_ <- Parser.pEmpty) yield Nil)

  def + : Parser[List[A]] = for {
    a <- this
    as <- this.*
  } yield a :: as

  def ? : Parser[Option[A]] = this.map[Option[A]](a => Some(a)) || Parser.pEmpty.map(_ => None)

  def intersperse[B](other : => Parser[B]) : Parser[List[A]] = for {
    a <- this
    b <- (for {
      _ <- other
      b <- this
    } yield b).*
  } yield a :: b

}