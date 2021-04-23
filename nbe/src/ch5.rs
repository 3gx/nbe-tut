#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Name),
    Lambda(Name, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Zero,
    Succ(Box<Expr>),
    Rec(Ty, Box<Expr>, Box<Expr>, Box<Expr>),
    Ann(Box<Expr>, Ty),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    TNat,
    TArr(Box<Ty>, Box<Ty>),
}

impl From<&Ty> for Box<Ty> {
    fn from(item: &Ty) -> Self {
        item.clone().into()
    }
}
impl From<&Expr> for Box<Expr> {
    fn from(item: &Expr) -> Self {
        item.clone().into()
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Name(pub String);
impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    VZero,
    VSucc(Box<Value>),
    VClosure(Env<Value>, Name, Expr),
    VNeutral(Ty, Neutral),
}

#[derive(Debug, Clone)]
pub enum Neutral {
    NVar(Name),
    NApp(Box<Neutral>, Box<Value>),
    NRec(Ty, Box<Neutral>, Normal, Normal),
}
#[derive(Debug, Clone)]
struct Normal(/*normal_type*/ Ty, /*normal_value*/ Box<Value>);

use std::collections::VecDeque;
pub type List<T> = VecDeque<T>;
pub macro list {
    ($($tt:tt)*) => {List::from(vec![$($tt)*])}
}

#[derive(Debug, Clone)]
pub struct Env<Val>(pub List<(Name, Val)>);

pub type Context = Env<Ty>;

impl<T> Env<T> {
    pub fn new() -> Self {
        Env(vec![].into_iter().collect())
    }
    pub fn map<F: Fn(T) -> T>(self, f: F) -> Self {
        let Env(vec) = self;
        let vec = vec.into_iter().map(move |(n, v)| (n, f(v))).collect();
        Env(vec)
    }
}

#[derive(Debug, Clone)]
pub struct Message(pub String);

pub macro failure {
    ($($tt:tt)*) => {Err(Message(format!($($tt)*)))}
}

pub fn lookup_var<'a, T>(Env(env): &'a Env<T>, Name(name): &Name) -> Result<&'a T, Message> {
    match env.iter().find(|(Name(n), _)| n == name) {
        Some((_, v)) => Ok(v),
        _ => failure!["Name not found: {:?}", name],
    }
}

pub fn extend<T: Clone>(Env(mut env): Env<T>, name: Name, val: T) -> Env<T> {
    env.push_front((name, val));
    Env(env)
}

pub fn eval(env: Env<Value>, e: Expr) -> Result<Value, Message> {
    use Expr::*;
    use Value::*;
    match e {
        Var(x) => lookup_var(&env, &x).map(|x| x.clone()),
        Lambda(x, box body) => Ok(VClosure(env, x, body)),
        App(box rator, box rand) => {
            let fun = eval(env.clone(), rator)?;
            let arg = eval(env, rand)?;
            do_apply(fun, arg)
        }
        other => panic!("unimplemented {:?}", other),
    }
}

pub fn do_apply(rator: Value, rand: Value) -> Result<Value, Message> {
    use Neutral::*;
    use Value::*;
    match (rator, rand) {
        (VClosure(env, x, body), arg) => eval(extend(env, x, arg), body),
        (VNeutral(neu), arg) => Ok(VNeutral(NApp(neu.into(), arg.into()))),
    }
}

pub fn freshen(used: &List<Name>, Name(name): Name) -> Name {
    let next_name = |Name(name): Name| Name(name + "'");
    for Name(n) in used.iter() {
        if n == &name {
            return next_name(Name(name));
        }
    }
    return Name(name);
}

fn cons<T>(x: T, mut list: List<T>) -> List<T> {
    list.push_front(x);
    list
}

fn read_back(used: List<Name>, val: Value) -> Result<Expr, Message> {
    use Expr::*;
    use Neutral::*;
    use Value::*;
    match val {
        VNeutral(NVar(x)) => Ok(Var(x)),
        VNeutral(NApp(box fun, box arg)) => {
            let rator = read_back(used.clone(), VNeutral(fun))?;
            let rand = read_back(used, arg)?;
            Ok(App(rator.into(), rand.into()))
        }
        VClosure(env, x, body) => {
            let fun = VClosure(env, x.clone(), body);
            let x = freshen(&used, x);
            let body_val = do_apply(fun, VNeutral(NVar(x.clone())))?;
            let body_expr = read_back(cons(x.clone(), used), body_val)?;
            Ok(Lambda(x, body_expr.into()))
        }
    }
}

pub fn normalize(expr: Expr) -> Result<Expr, Message> {
    let val = eval(Env::new(), expr)?;
    read_back(list![], val)
}

pub fn run_program(defs: List<(Name, Expr)>, expr: Expr) -> Result<Expr, Message> {
    let env = add_defs(Env::new(), defs.clone())?;
    let val = eval(env, expr)?;
    read_back(defs.into_iter().map(|(n, _)| n).collect(), val)
}

pub fn add_defs(env: Env<Value>, defs: List<(Name, Expr)>) -> Result<Env<Value>, Message> {
    defs.into_iter().fold(Ok(env), move |env, (x, e)| {
        let env = env?;
        let v = eval(env.clone(), e)?;
        Ok(extend(env, x, v))
    })
}
pub fn add_defs2ctx(ctx: Context, defs: List<(Name, Expr)>) -> Result<Context, Message> {
    defs.into_iter().fold(Ok(ctx), move |ctx, (x, e)| {
        let ctx = ctx?;
        let t = synth(&ctx, &e)?;
        Ok(extend(ctx, x, t))
    })
}

use std::collections::HashMap;
pub fn alpha_norm(e: Expr) -> Expr {
    fn gather(map: &mut HashMap<String, usize>, e: &Expr) {
        let mut add2map = |Name(name): &Name| {
            let idx = map.len();
            map.entry(name.clone()).or_insert(idx);
        };
        use Expr::*;
        match e {
            Var(n) => add2map(n),
            Lambda(n, box e) => {
                add2map(n);
                gather(map, e);
            }
            App(box rator, box rand) => {
                gather(map, rator);
                gather(map, rand);
            }
            _ => todo!(),
        }
    }
    let mut names = HashMap::new();
    gather(&mut names, &e);

    fn rename(map: &HashMap<String, usize>, e: Expr) -> Expr {
        use Expr::*;
        let new_name =
            |Name(name): Name| Name(format!("{}", map.len() - map.get(&name).unwrap() - 1));
        match e {
            Var(n) => Var(new_name(n)),
            Lambda(n, box e) => Lambda(new_name(n), rename(map, e).into()),
            App(box rator, box rand) => App(rename(map, rator).into(), rename(map, rand).into()),
            _ => todo!(),
        }
    }

    rename(&names, e)
}

pub fn synth(ctx: &Context, e: &Expr) -> Result<Ty, Message> {
    use {Expr::*, Ty::*};
    match e {
        Var(x) => lookup_var(ctx, x).map(|x| x.clone()),
        App(box rator, box rand) => match synth(ctx, rator)? {
            TArr(box arg_ty, box ret_ty) => {
                check(ctx, rand, &arg_ty)?;
                Ok(ret_ty)
            }
            other => failure!["not a funciton type: {:?}", other],
        },
        Rec(ty, box tgt, box base, box step) => {
            let tgt_ty = &synth(ctx, tgt)?;
            match tgt_ty {
                TNat => {
                    check(ctx, base, tgt_ty)?;
                    check(
                        ctx,
                        step,
                        &TArr(TNat.into(), TArr(ty.into(), ty.into()).into()),
                    )?;
                    Ok(ty.clone())
                }
                other => failure!["Not the type Nat: {:?}", other],
            }
        }
        Ann(box e, t) => {
            check(ctx, e, t)?;
            Ok(t.clone())
        }

        // failure to synthesize
        other => failure![
            "can't synthesize type for {:?}. Try adding type annotations",
            other
        ],
    }
}
pub fn check(ctx: &Context, e: &Expr, ty: &Ty) -> Result<(), Message> {
    use {Expr::*, Ty::*};
    match e {
        // lambda abstraction
        Lambda(x, box body) => match ty {
            TArr(box arg, box ret) => {
                check(&extend(ctx.clone(), x.clone(), arg.clone()), body, &ret)
            }
            other => failure!["Lambda requires function type, got {:?}", other],
        },

        // zero ctor
        Zero => match ty {
            TNat => Ok(()),
            other => failure!["Zer should be Nat, got {:?}", (other, ty)],
        },

        // successor
        Succ(box n) => match ty {
            TNat => check(ctx, n, &TNat),
            other => failure!["Succ should be Nat, got {:?}", (other, ty)],
        },

        // mode change
        other => {
            let ty1 = &synth(ctx, other)?;
            match ty == ty1 {
                true => Ok(()),
                false => failure!["{:?}: expected {:?}, but got {:?}", other, ty, ty1],
            }
        }
    }
}

// macros

pub macro typ {
    (tnat) => {Ty::TNat},
    (($t1:tt -> $t2:tt)) => {Ty::TArr(typ![$t1].into(),
                                    typ![$t2].into())}
}
pub macro expr {
    ((lam $var:ident $expr:tt)) => {
        Expr::Lambda(Name(stringify!($var).into()), expr![$expr].into())
    },
    (zero) => {Expr::Zero},
    ((succ $expr:tt)) => {Expr::Succ(expr![$expr].into())},
    ((rec [$typ:tt] $n:tt $b:tt $s:tt)) => {
        Expr::Rec(typ![$typ],
                  expr![$n].into(),
                  expr![$b].into(),
                  expr![$s].into())
    },
    ([$expr:tt : $typ:tt]) => {
        Expr::Ann(expr![$expr].into(),
                  typ![$typ])
    },
    (($rator:tt $rand:tt)) => {
        Expr::App(expr![$rator].into(), expr![$rand].into())
    },
    ($id:ident) => {
        Expr::Var(Name(stringify!($id).into()))
    },
    {$expr:expr} => {$expr},
}

pub macro def($id:ident <- $expr:tt) {
    (Name(stringify!($id).into()), expr![$expr])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t1() {
        let e1 = expr![(lam f (f (f f)))];
        let e1str = format!("{:?}", e1);
        println!("e1= {}", e1str);
        assert_eq!(
            e1str,
            "Lambda(\"f\", App(Var(\"f\"), App(Var(\"f\"), Var(\"f\"))))"
        );
    }

    #[test]
    fn ch15_churcle_numerals() -> Result<(), Message> {
        let church_defs = list![
            def![zero1 <- (lam f (lam x x))],
            def![add1 <- (lam n (lam f (lam x (f ((n f) x)))))],
            def![plus <- (lam j (lam k (lam f (lam x ((j f) ((k f) x))))))],
        ];
        fn to_church(n: usize) -> Expr {
            match n {
                0 => expr![zero1],
                _ => expr![(add1 {to_church(n-1)})],
            }
        }
        let e = expr![((plus {to_church(2)}) {to_church(3)})];
        let v = run_program(church_defs, e)?;
        println!("v= {:?}", v);
        let five = expr![(lam g (lam y (g (g (g (g (g y)))))))];
        println!("5= {:?}", alpha_norm(five.clone()));
        assert_eq!(alpha_norm(v), alpha_norm(five));
        Ok(())
    }

    #[test]
    fn types() {
        let e1 = expr!([(lam x (lam y y)) : (tnat -> (tnat -> tnat))]);
        let e1str = format!("{:?}", e1);
        println!("e= {}", e1str);
        assert_eq!(
            e1str,
            "Ann(Lambda(\"x\", Lambda(\"y\", Var(\"y\"))), TArr(TNat, TArr(TNat, TNat)))"
        );
    }

    #[test]
    fn types2() -> Result<(), Message> {
        use Ty::*;
        let ctx = list![
            def![two <- [(succ (succ zero)) : tnat]],
            def![three <- [(succ two) : tnat]],
            def![plus <- [(lam n
                               (lam k
                                    (rec [tnat]
                                         n
                                         k
                                         (lam pred
                                              (lam almostSum
                                                   (succ almostSum)))))) :
                          (tnat -> (tnat -> tnat))]]
        ];
        let ctx = add_defs2ctx(Context::new(), ctx)?;
        let e1 = expr![(plus three)];
        let t1 = synth(&ctx, &e1)?;
        println!("{:?} : {:?}", e1, t1);
        assert_eq!(t1, TArr(TNat.into(), TNat.into()));

        let e2 = expr![((plus three) two)];
        let t2 = synth(&ctx, &e2)?;
        println!("{:?} : {:?}", e2, t2);
        assert_eq!(t2, TNat);

        Ok(())
    }
}
