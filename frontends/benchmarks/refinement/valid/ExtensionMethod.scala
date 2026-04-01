import stainless.lang._

type Nat = {i:BigInt with 0 <= i}

def nat(i: BigInt): Nat = 
  require(0 <= i)
  i.asInstanceOf[Nat]

def plus(a:Nat,b:Nat) = (a+b).asInstanceOf[Nat]

extension (a:Nat)
  def +++(b: Nat): Nat = plus(a,b)

def cp[T](x: Nat): Nat =
  if x == 0 then x
  else nat(1) +++ nat(x-1)