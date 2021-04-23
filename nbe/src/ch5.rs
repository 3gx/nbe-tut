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
    NApp(Box<Neutral>, Box<Normal>),
    NRec(Ty, Box<Neutral>, Box<Normal>, Box<Normal>),
}
#[derive(Debug, Clone)]
pub struct Normal(pub Ty /*normal_type*/, pub Value /*normal_value*/);

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
    ($($tt:tt)*) => {Err(Message(format!("{}:{}:{}", file!(), line!(), format!($($tt)*))))}
}

fn lookup_var<'a, T>(Env(env): &'a Env<T>, Name(name): &Name) -> Result<&'a T, Message> {
    match env.iter().find(|(Name(n), _)| n == name) {
        Some((_, v)) => Ok(v),
        _ => failure!["Name not found: {:?}", name],
    }
}

fn extend<T: Clone>(Env(mut env): Env<T>, name: Name, val: T) -> Env<T> {
    env.push_front((name, val));
    Env(env)
}

fn eval(env: Env<Value>, e: Expr) -> Result<Value, Message> {
    use {Expr::*, Value::*};
    match e {
        Var(x) => lookup_var(&env, &x).map(|x| x.clone()),
        Lambda(x, box body) => Ok(VClosure(env, x, body)),
        App(box rator, box rand) => {
            let fun = eval(env.clone(), rator)?;
            let arg = eval(env, rand)?;
            do_apply(fun, arg)
        }
        Zero => Ok(VZero),
        Succ(box n) => Ok(VSucc(eval(env, n)?.into())),
        Rec(t, box tgt, box base, box step) => do_rec(
            t,
            eval(env.clone(), tgt)?,
            eval(env.clone(), base)?,
            eval(env, step)?,
        ),
        Ann(box e, _) => eval(env, e),
    }
}

fn do_apply(rator: Value, rand: Value) -> Result<Value, Message> {
    use {Neutral::*, Ty::*, Value::*};
    match (rator, rand) {
        (VClosure(env, x, body), arg) => eval(extend(env, x, arg), body),
        (VNeutral(TArr(box t1, box t2), neu), arg) => {
            Ok(VNeutral(t2, NApp(neu.into(), Normal(t1, arg).into())))
        }
        other => failure!["can't apply {:?}", other],
    }
}
fn do_rec(t: Ty, v: Value, base: Value, step: Value) -> Result<Value, Message> {
    use {Neutral::*, Ty::*, Value::*};
    match v {
        VZero => Ok(base),
        VSucc(box n) => do_apply(
            do_apply(step.clone(), n.clone())?,
            do_rec(t, n, base, step)?,
        ),
        VNeutral(TNat, neu) => Ok(VNeutral(
            t.clone(),
            NRec(
                t.clone(),
                neu.into(),
                Normal(t.clone(), base).into(),
                Normal(
                    TArr(TNat.into(), TArr(t.clone().into(), t.into()).into()),
                    step,
                )
                .into(),
            ),
        )),
        other => failure!["can't do_rec on {:?}", other],
    }
}

fn freshen(used: &List<Name>, Name(name): Name) -> Name {
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

fn read_back_normal(used: List<Name>, Normal(t, v): Normal) -> Result<Expr, Message> {
    read_back(used, t, v)
}

fn read_back_neutral(used: List<Name>, neu: Neutral) -> Result<Expr, Message> {
    use {Expr::*, Neutral::*};
    match neu {
        NVar(x) => Ok(Var(x)),
        NApp(box rator, box rand) => Ok(App(
            read_back_neutral(used.clone(), rator)?.into(),
            read_back_normal(used, rand)?.into(),
        )),
        NRec(t, box neu, box base, box step) => Ok(Rec(
            t,
            read_back_neutral(used.clone(), neu)?.into(),
            read_back_normal(used.clone(), base)?.into(),
            read_back_normal(used, step)?.into(),
        )),
    }
}

fn read_back(used: List<Name>, ty: Ty, val: Value) -> Result<Expr, Message> {
    use {Expr::*, Neutral::*, Ty::*, Value::*};
    match (ty, val) {
        (TNat, VZero) => Ok(Zero),
        (TNat, VSucc(box pred)) => Ok(Succ(read_back(used, TNat, pred)?.into())),
        (TArr(box t1, box t2), fun) => {
            fn arg_name(v: Value) -> Name {
                match v {
                    VClosure(_, x, _) => x,
                    _ => Name("x".into()),
                }
            }
            let x = freshen(&used, arg_name(fun.clone()));
            let xval = VNeutral(t1, NVar(x.clone()));
            Ok(Lambda(
                x.clone(),
                read_back(cons(x, used), t2, do_apply(fun, xval)?)?.into(),
            ))
        }
        (t1, VNeutral(t2, neu)) => {
            if t1 == t2 {
                read_back_neutral(used, neu)
            } else {
                failure!["Internal error: mismatched types {:?}", (t1, t2)]
            }
        }
        other => failure!["can't read pack {:?}", other],
    }
}

type Defs = Env<Normal>;

fn no_defs() -> Defs {
    Defs::new()
}

fn defs2ctx(Env(defs): Defs) -> Context {
    Env(defs.into_iter().map(|(n, Normal(t, _))| (n, t)).collect())
}
fn defs2env(Env(defs): Defs) -> Env<Value> {
    Env(defs.into_iter().map(|(n, Normal(_, v))| (n, v)).collect())
}

fn add_defs(defs: Defs, exprs: List<(Name, Expr)>) -> Result<Defs, Message> {
    exprs.into_iter().fold(Ok(defs), move |defs, (x, e)| {
        let defs = defs?;
        let norm = norm_with_defs(defs.clone(), e)?;
        Ok(extend(defs, x, norm))
    })
}

fn norm_with_defs(defs: Defs, e: Expr) -> Result<Normal, Message> {
    let t = synth(&defs2ctx(defs.clone()), &e)?;
    let v = eval(defs2env(defs), e)?;
    Ok(Normal(t, v))
}

fn defined_names(Env(defs): Defs) -> List<Name> {
    defs.into_iter().map(|(n, _)| n).collect()
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
            Zero => (),
            Succ(box expr) => gather(map, expr),
            Rec(_, box e1, box e2, box e3) => [e1, e2, e3].iter().for_each(|e| gather(map, e)),
            Ann(box e, _) => gather(map, e),
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
            Zero => Zero,
            Succ(box e) => Succ(rename(map, e).into()),
            Rec(ty, box e1, box e2, box e3) => Rec(
                ty,
                rename(map, e1).into(),
                rename(map, e2).into(),
                rename(map, e3).into(),
            ),
            Ann(box e, ty) => Ann(rename(map, e).into(), ty),
        }
    }

    rename(&names, e)
}

fn synth(ctx: &Context, e: &Expr) -> Result<Ty, Message> {
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

fn check(ctx: &Context, e: &Expr, ty: &Ty) -> Result<(), Message> {
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

pub fn norm_with_test_defs(e: Expr) -> Result<Expr, Message> {
    let defs = list![
        def! {two <- [(succ (succ zero)) : tnat]},
        def! {three <- [(succ (succ (succ zero))) : tnat]},
        def! {plus <- [(lam n
        (lam k
          (rec [tnat]
            n
            k
            (lam pred
              (lam almostSum
                (succ almostSum)))))) :
          (tnat -> (tnat -> tnat))]}
    ];
    let defs = add_defs(no_defs(), defs)?;
    let norm = norm_with_defs(defs.clone(), e)?;
    Ok(read_back_normal(defined_names(defs), norm)?)
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

    fn to_church(n: usize, base: Expr) -> Expr {
        match n {
            0 => expr![{ base }],
            _ => expr![(succ {to_church(n-1, base)})],
        }
    }

    #[test]
    fn t1() -> Result<(), Message> {
        let e = expr! { plus };
        let norm = norm_with_test_defs(e.clone())?;
        println!("{:?} ~> {:?}", e, norm);

        let e = expr! { (plus three) };
        let norm = norm_with_test_defs(e.clone())?;
        println!("{:?} ~> {:?}", e, norm);
        let egold = expr! { (lam x {to_church(3, expr![x])}) };
        assert_eq!(alpha_norm(norm), alpha_norm(egold));

        let e = expr! { ((plus three) two) };
        let norm = norm_with_test_defs(e.clone())?;
        println!("{:?} ~> {:?}", e, norm);
        let egold = to_church(5, expr![zero]);
        assert_eq!(alpha_norm(norm), alpha_norm(egold));

        Ok(())
    }
}
