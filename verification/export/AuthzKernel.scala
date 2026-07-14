object AuthzKernel {

abstract sealed class nat
final case class Nat(a : BigInt) extends nat

def integer_of_nat(x0 : nat) : BigInt = x0 match {
  case Nat(x) => x
}

def equal_nata(m : nat, n : nat) : Boolean =
  integer_of_nat(m) == integer_of_nat(n)

trait equal[A] {
  val `AuthzKernel.equal` : (A, A) => Boolean
}
def equal[A](a : A, b : A)(implicit A: equal[A]) : Boolean =
  A.`AuthzKernel.equal`(a, b)
object equal {
  implicit def `AuthzKernel.equal_prod`[A : equal, B : equal] : equal[(A, B)] =
    new equal[(A, B)] {
    val `AuthzKernel.equal` = (a : (A, B), b : (A, B)) =>
      equal_proda[A, B](a, b)
  }
  implicit def `AuthzKernel.equal_rel` : equal[rel] = new equal[rel] {
    val `AuthzKernel.equal` = (a : rel, b : rel) => equal_rela(a, b)
  }
  implicit def `AuthzKernel.equal_vl` : equal[vl] = new equal[vl] {
    val `AuthzKernel.equal` = (a : vl, b : vl) => equal_vla(a, b)
  }
  implicit def `AuthzKernel.equal_bool` : equal[Boolean] = new equal[Boolean] {
    val `AuthzKernel.equal` = (a : Boolean, b : Boolean) => equal_boola(a, b)
  }
  implicit def `AuthzKernel.equal_set`[A : equal] : equal[set[A]] = new
    equal[set[A]] {
    val `AuthzKernel.equal` = (a : set[A], b : set[A]) => equal_seta[A](a, b)
  }
  implicit def `AuthzKernel.equal_nat` : equal[nat] = new equal[nat] {
    val `AuthzKernel.equal` = (a : nat, b : nat) => equal_nata(a, b)
  }
}

def list_all[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

abstract sealed class set[A]
final case class seta[A](a : List[A]) extends set[A]
final case class coset[A](a : List[A]) extends set[A]

def eq[A : equal](a : A, b : A) : Boolean = equal[A](a, b)

def membera[A : equal](x0 : List[A], y : A) : Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def member[A : equal](x : A, xa1 : set[A]) : Boolean = (x, xa1) match {
  case (x, seta(xs)) => membera[A](xs, x)
  case (x, coset(xs)) => ! (membera[A](xs, x))
}

def less_eq_set[A : equal](a : set[A], b : set[A]) : Boolean = (a, b) match {
  case (seta(xs), b) => list_all[A](((x : A) => member[A](x, b)), xs)
  case (a, coset(ys)) => list_all[A](((y : A) => ! (member[A](y, a))), ys)
  case (coset(Nil), seta(Nil)) => false
}

def equal_seta[A : equal](a : set[A], b : set[A]) : Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

def equal_boola(p : Boolean, pa : Boolean) : Boolean = (p, pa) match {
  case (false, p) => ! p
  case (true, p) => p
  case (p, false) => ! p
  case (p, true) => p
}

abstract sealed class vl
final case class Ent(a : nat) extends vl
final case class Lit(a : nat) extends vl

def equal_vla(x0 : vl, x1 : vl) : Boolean = (x0, x1) match {
  case (Ent(x1), Lit(x2)) => false
  case (Lit(x2), Ent(x1)) => false
  case (Lit(x2), Lit(y2)) => equal_nata(x2, y2)
  case (Ent(x1), Ent(y1)) => equal_nata(x1, y1)
}

abstract sealed class rel
final case class Fwd(a : nat) extends rel
final case class Rev(a : nat) extends rel

def equal_rela(x0 : rel, x1 : rel) : Boolean = (x0, x1) match {
  case (Fwd(x1), Rev(x2)) => false
  case (Rev(x2), Fwd(x1)) => false
  case (Rev(x2), Rev(y2)) => equal_nata(x2, y2)
  case (Fwd(x1), Fwd(y1)) => equal_nata(x1, y1)
}

def equal_proda[A : equal, B : equal](x0 : (A, B), x1 : (A, B)) : Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

trait ord[A] {
  val `AuthzKernel.less_eq` : (A, A) => Boolean
  val `AuthzKernel.less` : (A, A) => Boolean
}
def less_eq[A](a : A, b : A)(implicit A: ord[A]) : Boolean =
  A.`AuthzKernel.less_eq`(a, b)
def less[A](a : A, b : A)(implicit A: ord[A]) : Boolean =
  A.`AuthzKernel.less`(a, b)
object ord {
  implicit def `AuthzKernel.ord_integer` : ord[BigInt] = new ord[BigInt] {
    val `AuthzKernel.less_eq` = (a : BigInt, b : BigInt) => a <= b
    val `AuthzKernel.less` = (a : BigInt, b : BigInt) => a < b
  }
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a : num) extends num
final case class Bit1(a : num) extends num

abstract sealed class check
final case class Terminal(a : rel) extends check
final case class Chain(a : rel, b : nat) extends check
final case class AttrEq(a : nat, b : vl) extends check
final case class CNot(a : check) extends check
final case class CAnd(a : check, b : check) extends check
final case class COr(a : check, b : check) extends check

abstract sealed class reg_ext[A]
final case class reg_exta[A](a : nat => rel => Option[nat],
                              b : nat => nat => Option[check], c : A)
  extends reg_ext[A]

def plus_nat(m : nat, n : nat) : nat =
  Nat(integer_of_nat(m) + integer_of_nat(n))

def one_nat : nat = Nat(BigInt(1))

def Suc(n : nat) : nat = plus_nat(n, one_nat)

def Ball[A](x0 : set[A], p : A => Boolean) : Boolean = (x0, p) match {
  case (seta(xs), p) => list_all[A](p, xs)
}

def fold[A, B](f : A => B => B, x1 : List[A], s : B) : B = (f, x1, s) match {
  case (f, Nil, s) => s
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
}

def maps[A, B](f : A => List[B], x1 : List[A]) : List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def map[A, B](f : A => B, x1 : List[A]) : List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def image[A, B](f : A => B, x1 : set[A]) : set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def map_of[A : equal, B](x0 : List[(A, B)], k : A) : Option[B] = (x0, k) match {
  case (Nil, k) => None
  case ((l, v) :: ps, k) =>
    (eq[A](l, k) match { case true => Some[B](v)
      case false => map_of[A, B](ps, k) })
}

def filtera[A](p : A => Boolean, x1 : List[A]) : List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) =>
    (p(x) match { case true => x :: filtera[A](p, xs)
      case false => filtera[A](p, xs) })
}

def filter[A](p : A => Boolean, x1 : set[A]) : set[A] = (p, x1) match {
  case (p, seta(xs)) => seta[A](filtera[A](p, xs))
}

def removeAll[A : equal](x : A, xa1 : List[A]) : List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (eq[A](x, y) match { case true => removeAll[A](x, xs)
      case false => y :: removeAll[A](x, xs) })
}

def inserta[A : equal](x : A, xs : List[A]) : List[A] =
  (membera[A](xs, x) match { case true => xs case false => x :: xs })

def insert[A : equal](x : A, xa1 : set[A]) : set[A] = (x, xa1) match {
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
}

def list_ex[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def product[A, B](x0 : List[A], uu : List[B]) : List[(A, B)] = (x0, uu) match {
  case (Nil, uu) => Nil
  case (x :: xs, ys) =>
    map[B, (A, B)](((a : B) => (x, a)), ys) ++ product[A, B](xs, ys)
}

def distinct[A : equal](x0 : List[A]) : Boolean = x0 match {
  case Nil => true
  case x :: xs => ! (membera[A](xs, x)) && distinct[A](xs)
}

def map_filter[A, B](f : A => Option[B], x1 : List[A]) : List[B] = (f, x1)
  match {
  case (f, Nil) => Nil
  case (f, x :: xs) => (f(x) match {
                          case None => map_filter[A, B](f, xs)
                          case Some(y) => y :: map_filter[A, B](f, xs)
                        })
}

def kext(ds : List[(nat, (nat, vl))], r : rel) : List[(nat, nat)] =
  (r match {
     case Fwd(a) =>
       maps[(nat, (nat, vl)),
             (nat, nat)](((b : (nat, (nat, vl))) =>
                           (b match {
                              case (e, (aa, Ent(y))) =>
                                (equal_nata(aa, a) match {
                                  case true => List((e, y)) case false => Nil })
                              case (_, (_, Lit(_))) => Nil
                            })),
                          ds)
     case Rev(a) =>
       maps[(nat, (nat, vl)),
             (nat, nat)](((b : (nat, (nat, vl))) =>
                           (b match {
                              case (e, (aa, Ent(y))) =>
                                (equal_nata(aa, a) match {
                                  case true => List((y, e)) case false => Nil })
                              case (_, (_, Lit(_))) => Nil
                            })),
                          ds)
   })

def bot_set[A] : set[A] = seta[A](Nil)

def max[A : ord](a : A, b : A) : A =
  (less_eq[A](a, b) match { case true => b case false => a })

def minus_nat(m : nat, n : nat) : nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def zero_nat : nat = Nat(BigInt(0))

def fixloop[A : equal](m : nat, f : A => A, x : A) : A =
  (equal_nata(m, zero_nat) match { case true => x
    case false => {
                    val xa = f(x) : A;
                    (eq[A](xa, x) match { case true => x
                      case false => fixloop[A](minus_nat(m, one_nat), f, xa) })
                  }
    })

def length_tailrec[A](x0 : List[A], n : nat) : nat = (x0, n) match {
  case (Nil, n) => n
  case (x :: xs, n) => length_tailrec[A](xs, Suc(n))
}

def size_list[A](xs : List[A]) : nat = length_tailrec[A](xs, zero_nat)

def times_nat(m : nat, n : nat) : nat =
  Nat(integer_of_nat(m) * integer_of_nat(n))

def kadom(ds : List[(nat, (nat, vl))]) : List[nat] =
  map[(nat, (nat, vl)),
       nat](((a : (nat, (nat, vl))) =>
              {
                val (e, (_, _)) = a : ((nat, (nat, vl)));
                e
              }),
             ds) ++
    maps[(nat, (nat, vl)),
          nat](((a : (nat, (nat, vl))) => (a match {
     case (_, (_, Ent(y))) => List(y)
     case (_, (_, Lit(_))) => Nil
   })),
                ds)

def kiters(kp : List[((nat, nat), check)], ds : List[(nat, (nat, vl))]) : nat =
  Suc(times_nat(size_list[((nat, nat), check)](kp),
                 times_nat(size_list[nat](kadom(ds)),
                            size_list[nat](kadom(ds)))))

def sup_set[A : equal](x0 : set[A], a : set[A]) : set[A] = (x0, a) match {
  case (seta(xs), a) =>
    fold[A, set[A]](((aa : A) => (b : set[A]) => insert[A](aa, b)), xs, a)
  case (coset(xs), a) =>
    coset[A](filtera[A](((x : A) => ! (member[A](x, a))), xs))
}

def fst[A, B](x0 : (A, B)) : A = x0 match {
  case (x1, x2) => x1
}

def rels[A](x0 : reg_ext[A]) : nat => rel => Option[nat] = x0 match {
  case reg_exta(rels, perms, more) => rels
}

def ksat(gamma : reg_ext[Unit], ds : List[(nat, (nat, vl))],
          i : set[((nat, nat), (nat, nat))], t : nat, x4 : check, s : nat,
          ob : nat) : Boolean
  =
  (gamma, ds, i, t, x4, s, ob) match {
  case (gamma, ds, i, t, Terminal(r), s, ob) =>
    membera[(nat, nat)](kext(ds, r), (ob, s))
  case (gamma, ds, i, t, Chain(r, q), s, ob) =>
    ((rels[Unit](gamma)).apply(t).apply(r) match {
       case None => false
       case Some(ta) =>
         list_ex[(nat, nat)](((a : (nat, nat)) =>
                               {
                                 val (x, m) = a : ((nat, nat));
                                 equal_nata(x, ob) &&
                                   member[((nat, nat),
    (nat, nat))](((ta, q), (s, m)), i)
                               }),
                              kext(ds, r))
     })
  case (gamma, ds, i, t, AttrEq(a, v), s, ob) =>
    membera[(nat, (nat, vl))](ds, (ob, (a, v)))
  case (gamma, ds, i, t, CNot(c), s, ob) => ! (ksat(gamma, ds, i, t, c, s, ob))
  case (gamma, ds, i, t, CAnd(c1, c2), s, ob) =>
    ksat(gamma, ds, i, t, c1, s, ob) && ksat(gamma, ds, i, t, c2, s, ob)
  case (gamma, ds, i, t, COr(c1, c2), s, ob) =>
    ksat(gamma, ds, i, t, c1, s, ob) || ksat(gamma, ds, i, t, c2, s, ob)
}

def kstep(gamma : reg_ext[Unit], ds : List[(nat, (nat, vl))],
           sigma : ((nat, nat)) => nat, kp : List[((nat, nat), check)], n : nat,
           l : set[((nat, nat), (nat, nat))],
           j : set[((nat, nat), (nat, nat))]) : set[((nat, nat), (nat, nat))]
  =
  sup_set[((nat, nat),
            (nat, nat))](l, seta[((nat, nat),
                                   (nat, nat))](maps[((nat, nat), check),
              ((nat, nat),
                (nat, nat))](((a : ((nat, nat), check)) =>
                               {
                                 val (k, c) = a : (((nat, nat), check));
                                 (equal_nata(sigma(k), n) match {
                                   case true => map_filter[(nat, nat),
                    ((nat, nat),
                      (nat, nat))](((x : (nat, nat)) =>
                                     ({
val (aa, b) = x : ((nat, nat));
ksat(gamma, ds,
      sup_set[((nat, nat),
                (nat, nat))](l, filter[((nat, nat),
 (nat, nat))](((y : ((nat, nat), (nat, nat))) =>
                equal_nata(sigma(fst[(nat, nat), (nat, nat)](y)), n)),
               j)),
      fst[nat, nat](k), c, aa, b)
                                      } match {
                                       case true => Some[((nat, nat),
                   (nat, nat))]({
                                  val (s, ob) = x : ((nat, nat));
                                  (k, (s, ob))
                                })
                                       case false => None })),
                                    product[nat, nat](kadom(ds), kadom(ds)))
                                   case false => Nil })
                               }),
                              kp)))

def kfix(gamma : reg_ext[Unit], ds : List[(nat, (nat, vl))],
          sigma : ((nat, nat)) => nat, kp : List[((nat, nat), check)], n : nat,
          l : set[((nat, nat), (nat, nat))]) : set[((nat, nat), (nat, nat))]
  =
  fixloop[set[((nat, nat),
                (nat, nat))]](kiters(kp, ds),
                               ((a : set[((nat, nat), (nat, nat))]) =>
                                 kstep(gamma, ds, sigma, kp, n, l, a)),
                               bot_set[((nat, nat), (nat, nat))])

def deps(gamma : reg_ext[Unit], t : nat,
          x2 : check) : set[((nat, nat), Boolean)]
  =
  (gamma, t, x2) match {
  case (gamma, t, Terminal(r)) => bot_set[((nat, nat), Boolean)]
  case (gamma, t, Chain(r, q)) =>
    ((rels[Unit](gamma)).apply(t).apply(r) match {
       case None => bot_set[((nat, nat), Boolean)]
       case Some(ta) =>
         insert[((nat, nat),
                  Boolean)](((ta, q), false), bot_set[((nat, nat), Boolean)])
     })
  case (gamma, t, AttrEq(a, v)) => bot_set[((nat, nat), Boolean)]
  case (gamma, t, CNot(c)) =>
    image[((nat, nat), Boolean),
           ((nat, nat),
             Boolean)](((a : ((nat, nat), Boolean)) =>
                         {
                           val (k, _) = a : (((nat, nat), Boolean));
                           (k, true)
                         }),
                        deps(gamma, t, c))
  case (gamma, t, CAnd(c1, c2)) =>
    sup_set[((nat, nat), Boolean)](deps(gamma, t, c1), deps(gamma, t, c2))
  case (gamma, t, COr(c1, c2)) =>
    sup_set[((nat, nat), Boolean)](deps(gamma, t, c1), deps(gamma, t, c2))
}

def generative(x0 : check) : Boolean = x0 match {
  case Terminal(r) => true
  case Chain(r, q) => true
  case AttrEq(a, v) => false
  case CNot(c) => false
  case CAnd(c1, c2) => generative(c1) || generative(c2)
  case COr(c1, c2) => generative(c1) && generative(c2)
}

def ksafe(kp : List[((nat, nat), check)]) : Boolean =
  list_all[((nat, nat),
             check)](((a : ((nat, nat), check)) =>
                       {
                         val (_, aa) = a : (((nat, nat), check));
                         generative(aa)
                       }),
                      kp)

def mkreg(kr : List[((nat, rel), nat)],
           kp : List[((nat, nat), check)]) : reg_ext[Unit]
  =
  reg_exta[Unit](((t : nat) => (r : rel) =>
                   map_of[(nat, rel), nat](kr, (t, r))),
                  ((t : nat) => (p : nat) =>
                    map_of[(nat, nat), check](kp, (t, p))),
                  ())

def ksigma(ks : List[((nat, nat), nat)]) : ((nat, nat)) => nat =
  ((k : (nat, nat)) => (map_of[(nat, nat), nat](ks, k) match {
                          case None => zero_nat
                          case Some(n) => n
                        }))

def ktower(gamma : reg_ext[Unit], ds : List[(nat, (nat, vl))],
            sigma : ((nat, nat)) => nat, kp : List[((nat, nat), check)],
            n : nat) : set[((nat, nat), (nat, nat))]
  =
  (equal_nata(n, zero_nat) match {
    case true => kfix(gamma, ds, sigma, kp, zero_nat,
                       bot_set[((nat, nat), (nat, nat))])
    case false => kfix(gamma, ds, sigma, kp, Suc(minus_nat(n, one_nat)),
                        ktower(gamma, ds, sigma, kp, minus_nat(n, one_nat)))
    })

def less_eq_nat(m : nat, n : nat) : Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

def less_nat(m : nat, n : nat) : Boolean = integer_of_nat(m) < integer_of_nat(n)

def kstratified(gamma : reg_ext[Unit], sigma : ((nat, nat)) => nat,
                 kp : List[((nat, nat), check)]) : Boolean
  =
  list_all[((nat, nat),
             check)](((a : ((nat, nat), check)) =>
                       {
                         val (k, c) = a : (((nat, nat), check));
                         Ball[((nat, nat),
                                Boolean)](deps(gamma, fst[nat, nat](k), c),
   ((aa : ((nat, nat), Boolean)) =>
     (aa match {
        case (ka, true) => less_nat(sigma(ka), sigma(k))
        case (ka, false) => less_eq_nat(sigma(ka), sigma(k))
      })))
                       }),
                      kp)

def kernel_check(kr : List[((nat, rel), nat)], kp : List[((nat, nat), check)],
                  ks : List[((nat, nat), nat)], ds : List[(nat, (nat, vl))],
                  s : nat, t : nat, p : nat, ob : nat) : Option[Boolean]
  =
  {
    val gamma = mkreg(kr, kp) : (reg_ext[Unit])
    val sigma = ksigma(ks) : (((nat, nat)) => nat);
    (distinct[(nat, nat)](map[((nat, nat), check),
                               (nat, nat)](((a : ((nat, nat), check)) =>
     fst[(nat, nat), check](a)),
    kp)) &&
       (kstratified(gamma, sigma, kp) && ksafe(kp)) match {
      case true => Some[Boolean](member[((nat, nat),
  (nat, nat))](((t, p), (s, ob)), ktower(gamma, ds, sigma, kp, sigma((t, p)))))
      case false => None })
  }

def nat_of_integer(k : BigInt) : nat = Nat(max[BigInt](BigInt(0), k))

} /* object AuthzKernel */
