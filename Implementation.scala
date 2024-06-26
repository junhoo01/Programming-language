package kuplrg

object Implementation extends Template {

  import Expr.*
  import Value.*
  import Inst.*
  import Control.*

  // ---------------------------------------------------------------------------
  // Problem #1
  // ---------------------------------------------------------------------------
  def reduce(st: State): State =
    val State(k, s, h, mem) = st
    k match{
      case Nil => st

      case current_k::remain_k =>
      current_k match {



        case IEval(env, EUndef) => (State(remain_k, UndefV :: s, h, mem))


        case IEval(env, ENum(n)) => (State(remain_k, NumV(n) :: s, h, mem))


        case IEval(env, EBool(n)) => (State(remain_k, BoolV(n) :: s, h, mem))


        case IEval(env, EAdd(l, r)) => (State(IEval(env,l)::IEval(env,r)::IAdd::remain_k,s,h,mem))

        case IAdd => 
          s match {
            case NumV(r) :: NumV(l) :: rest => (State(remain_k,NumV(l+r)::rest,h,mem))
            case _ => error(s"error")
          }


        case IEval(env, EMul(l, r)) => (State(IEval(env,l)::IEval(env,r)::IMul::remain_k,s,h,mem))

        case IMul => 
          s match {
            case NumV(r) :: NumV(l) :: rest => (State(remain_k,NumV(l*r)::rest,h,mem))
            case _ => error(s"error")
          }


        case IEval(env, EDiv(l, r)) => (State(IEval(env,l)::IEval(env,r)::IDiv::remain_k,s,h,mem))

        case IDiv => 
          s match {
            case NumV(r) :: NumV(l) :: rest => r match {
              case 0 => error(s"error")
              case _ => (State(remain_k,NumV(l/r)::rest,h,mem))
            }
            case _ => error(s"error")
          }        


        case IEval(env, EMod(l, r)) => (State(IEval(env,l)::IEval(env,r)::IMod::remain_k,s,h,mem))

        case IMod => 
          s match {
            case NumV(r) :: NumV(l) :: rest => r match {
              case 0 => error(s"error")
              case _ => (State(remain_k,NumV(l%r)::rest,h,mem))
            }
            case _ => error(s"error")
          }          


        case IEval(env, EEq(l, r)) => (State(IEval(env,l)::IEval(env,r)::IEq ::remain_k,s,h,mem))
        
        case IEq =>
          s match{ 
          case r::l::rest => (State(remain_k,BoolV(eq(l,r))::rest,h,mem))
          case _ => error(s"error")
          }


        case IEval(env, ELt(l, r)) => (State(IEval(env,l)::IEval(env,r)::ILt ::remain_k,s,h,mem))

        case ILt => 
          s match {
            case NumV(r) :: NumV(l) :: rest => (State(remain_k,BoolV(l<r)::rest,h,mem))
            case _ => error(s"error5")

          }


        case IEval(env, EVar(name, init, body)) => (State(IEval(env,init)::IDef(List(name), env, body)::remain_k,s,h,mem))

        case IDef(names, env, body) => 
          val addrlist = malloc(mem, names.length)
          val bindings = names.zip(addrlist).toMap
          val addrValueMap = addrlist.zip(s.take(names.length).reverse).toMap

          (State(IEval(env ++ bindings, body) :: remain_k, s.drop(names.length), h, mem ++ addrValueMap))

        case IEval(env, EId(name)) => (State(remain_k,mem.getOrElse(lookup(env,name),error(s"error1"))::s,h,mem))
 
        case IEval(env, EAssign(name, expr)) => (State(IEval(env,expr)::IWrite(lookup(env,name))::remain_k,s,h,mem))
 
        case IWrite(addr) =>   
        s match {
          case value :: rest => (State(remain_k, s, h, mem + (addr -> value)))
          case _ => error(s"error")
        }
        case IEval(env, ESeq(l, r)) => (State(IEval(env,l)::IPop::IEval(env,r) ::remain_k,s,h,mem))

        case IPop => 
        val value :: rest = s 
        (State(remain_k, rest, h, mem))
        

        case IEval(env, EIf(cond, thenExpr, elseExpr)) => 
        (State(IEval(env,cond)::IJmpIf(KValue(IEval(env, thenExpr)::remain_k, s, h))::IEval(env, elseExpr)::remain_k,s,h,mem))
      
        case IJmpIf(KValue(k1, s1, h1)) => 
        s match {
          case value :: rest => 
          value match {
            case BoolV(true) => (State(k1,s1,h1,mem))
            case BoolV(false) => (State(remain_k,rest,h,mem))
            case _ => error(s"error")
          }
          case _ => error(s"error")
        }

        case IEval(env, EWhile(cond, body)) => 
        val handle1 = h + (Continue->KValue(IPop::IEval(env,EWhile(cond,body))::remain_k,s,h)) + (Break->KValue(remain_k,s,h))
        val kvalue1 = KValue(IEval(env,body)::IJmp(Continue)::Nil,s,handle1)
        ((State(IEval(env, cond)::IJmpIf(kvalue1)::remain_k,UndefV::s,h,mem)))


        case IEval(env, EBreak) => (State(IJmp(Break)::Nil,UndefV::s,h,mem))


        case IEval(env, EContinue) => (State(IJmp(Continue)::Nil,UndefV::s,h,mem))
             

        case IEval(env, EFun(params, body)) => (State(remain_k,CloV(params, body, env)::s,h,mem))


        case IEval(env, EApp(fun, args)) =>
        val argEvals = args.map(arg => IEval(env, arg))
        (State(IEval(env,fun)::argEvals++(ICall(args.length)::remain_k),s,h,mem))



        case IEval(env, ETry(body, catchParam, catchExpr)) =>
        val h_body = h + (Throw -> KValue(IDef(List(catchParam), env, catchExpr)::remain_k,s,h)) + (Finally ->KValue(remain_k,s,h))
        (State(IEval(env,body)::IJmp(Finally)::Nil,s,h_body,mem))


        case IEval(env, EThrow(expr)) =>
        (State(IEval(env, expr)::IJmp(Throw)::Nil,s,h,mem))


        case IEval(env, EGen(params, body)) =>
        (State(remain_k,GenV(params, body, env)::s,h,mem))

        case IEval(env, EIterNext(iter, arg)) =>
        
        arg match{
          case None => 
          (State(IEval(env,iter)::IEval(env, EUndef)::INext::remain_k,s,h,mem))
          case Some(value) => (State(IEval(env,iter)::IEval(env,value)::INext::remain_k,s,h,mem))
        }


        case IEval(env, EYield(expr)) =>

        (State(IEval(env,expr)::IYield::Nil,BoolV(false)::ContV(KValue(remain_k,s,h))::s,h,mem))


        case IEval(env, EValueField(result)) => (State(IEval(env, result)::IValueField::remain_k,s,h,mem))

        case IEval(env, EDoneField(result)) => (State(IEval(env,result)::IDoneField::remain_k,s,h,mem))

        case ICall(argsize) => 

        val args = s.take(argsize)
        val rest_help = s.drop(argsize)
        val function::rest = rest_help

        function match{

        case CloV(params, body, funenv) =>
          val s_body = 
            if (argsize >= params.length) args.takeRight(params.length)
            else (List.fill(params.length-argsize)(UndefV) ::: args)

          (State(IDef(params, funenv, EReturn(body))::Nil,s_body,h-Break-Continue-Yield+(Return->KValue(remain_k,rest,h)),mem))

        case GenV(params, body, funenv) =>
          val a = malloc(mem)

          val k_body = IPop::IDef(params, funenv, EReturn(ETry(body,"tmpr",EId("tmpr"))))::Nil
          val s_body = 
            if (argsize >= params.length) args.takeRight(params.length)
            else (List.fill(params.length-argsize)(UndefV) ::: args)
          (State(remain_k,IterV(a)::rest,h,mem + (a -> ContV(KValue(k_body,s_body,Map())))))

        case _ => error(s"error")

        }  

        case IEval(env, EReturn(expr)) => (State(IEval(env,expr)::IReturn::remain_k,s,h,mem))



        
        case INext =>
        val value::IterV(a)::rest = s
        val ContV(KValue(k_1,s_1,h_1)) = mem.getOrElse(a,error(s"error"))
        val h_body = h_1 + (Yield -> KValue(remain_k,IterV(a)::rest,h)) + (Return -> KValue(remain_k,IterV(a)::rest,h))

        (State(k_1,value::s_1,h_body,mem)) 

        case IJmp(control) =>

        val value::rest = s
        val KValue(cont,stack,handler) = lookup(h,control)
        val updatehandler =
          if (h.contains(Yield)) handler + (Yield -> lookup(h,Yield))
          else handler
        
        (State(cont, value::stack, updatehandler,mem))


        case IReturn => 
        val value::rest = s
          if (h.contains(Yield)) 
          (State(IYield::Nil, value::BoolV(true)::ContV(KValue(IReturn::Nil,Nil,Map()))::rest,h,mem))
          else (State(IJmp(Return)::Nil,value::Nil,h,mem))        

        case IYield =>
        val value_1::BoolV(b)::value_2::rest = s
        val KValue(k_1,IterV(a)::s_1,h_1) = lookup(h,Yield)
        
        (State(k_1,ResultV(value_1,b)::s_1,h_1,mem +(a->value_2)))


        case IValueField => 
        val ResultV(value, done)::rest = s
        (State(remain_k, value::rest, h, mem))

        case IDoneField =>
        val ResultV(value, done)::rest = s
        (State(remain_k,BoolV(done)::rest,h,mem))

      }
    }
  
  // ---------------------------------------------------------------------------
  // Problem #2
  // ---------------------------------------------------------------------------
  def bodyOfSquares: String = { """

  var x = from;

  while (x <= to) {
    yield x * x;
    x = x + 1;
  }

    
    """
  }

  // ---------------------------------------------------------------------------
  // Helper functions
  // ---------------------------------------------------------------------------
  def malloc(mem: Mem, n: Int): List[Addr] =
    val a = malloc(mem)
    (0 until n).toList.map(a + _)

  def malloc(mem: Mem): Addr = mem.keySet.maxOption.fold(0)(_ + 1)

  def lookup(env: Env, x: String): Addr =
    env.getOrElse(x, error(s"free identifier: $x"))

  def lookup(handler: Handler, x: Control): KValue =
    handler.getOrElse(x, error(s"invalid control operation: $x"))

  def eq(l: Value, r: Value): Boolean = (l, r) match
    case (UndefV, UndefV) => true
    case (NumV(l), NumV(r)) => l == r
    case (BoolV(l), BoolV(r)) => l == r
    case (IterV(l), IterV(r)) => l == r
    case (ResultV(lv, ld), ResultV(rv, rd)) => eq(lv, rv) && ld == rd
    case _ => false


  
}

  