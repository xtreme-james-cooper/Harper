package src

object Parser {
  
  def pEmpty : Parser[Unit] = new Parser(s => List(((), s)))
  
  def pSat(b : String => Boolean) : Parser[String] = new Parser({
    case tok::toks if b(tok) => List((tok, toks))
    case _ => Nil
  })
  
  def pLit(s : String) : Parser[String] = pSat(_ == s)
  
  def pIdent : Parser[String] = pSat(s => s.head.isLowerCase || s.head == '_')
  
  def pUpperIdent : Parser[String] = pSat(s => s.head.isUpperCase)
  
  def pEnd : Parser[Unit] = new Parser({
    case tok::toks => Nil
    case Nil => List(((), Nil))
  })
  
}

class Parser[A](val run : List[String] => List[(A, List[String])]) {
  
  def or(other : => Parser[A]) : Parser[A] = new Parser(s => run(s) ++ other.run(s))
  
  def then[B, C](op : A => B => C)(other : => Parser[B]) : Parser[C] = new Parser(s =>
    for {
      (v1, toks) <- run(s)
      (v2, toks2) <- other.run(toks)
    } yield (op(v1)(v2), toks2))
  
  def thenK[B](other : => Parser[B]) : Parser[A] = then[B, A](a => b => a)(other)
  def thenJ[B](other : => Parser[B]) : Parser[B] = then[B, B](a => b => b)(other)
  def thenS[B](other : => Parser[B]) : Parser[(A, B)] = then[B, (A, B)](a => b => (a, b))(other)
  
  def appl[B](op : A => B) : Parser[B] = new Parser(s =>
    for {
      (v, toks) <- run(s)
    } yield (op(v), toks))
  
  def star : Parser[List[A]] = (this plus) or (Parser.pEmpty appl (_ => Nil))
    
  def plus : Parser[List[A]] = this.then[List[A], List[A]](a => b => a :: b)(this.star)
  
  def intersperse[B](other : => Parser[B]) : Parser[List[A]] = this.then[List[A], List[A]](a => b => a :: b)((other thenJ this).star)
}