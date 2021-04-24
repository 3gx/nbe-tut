#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Name),
    Lambda(Name, BoxedExpr),
    App(BoxedExpr, BoxedExpr),
}
#[derive(Clone, PartialEq, Eq)]
pub struct Name(pub String);
impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

pub type BoxedExpr = Box<Expr>;

impl From<BoxedExpr> for Expr {
    fn from(item: BoxedExpr) -> Self {
        *item
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    VClosure(Env<Value>, Name, Expr),
    VNeutral(Neutral),
}

#[derive(Debug, Clone)]
pub enum Neutral {
    NVar(Name),
    NApp(Box<Neutral>, Box<Value>),
}

use std::collections::VecDeque;
pub type List<T> = VecDeque<T>;
pub macro list {
    ($($tt:tt)*) => {List::from(vec![$($tt)*])}
}

#[derive(Debug, Clone)]
pub struct Env<Val>(pub List<(Name, Val)>);

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

pub fn failure<T>(msg: String) -> Result<T, Message> {
    Err(Message(msg))
}

pub fn lookup_var<'a>(Env(env): &'a Env<Value>, Name(name): &Name) -> Result<&'a Value, Message> {
    match env.iter().find(|(Name(n), _)| n == name) {
        Some((_, v)) => Ok(v),
        _ => Err(Message(format!("Name not found: {:?}", name))),
    }
}

pub fn extend<Val: Clone>(Env(mut env): Env<Val>, name: Name, val: Val) -> Env<Val> {
    env.push_front((name, val));
    Env(env)
}

pub fn eval(env: Env<Value>, e: Expr) -> Result<Value, Message> {
    use Expr::*;
    use Value::*;
    dbg!(e.clone());
    match e {
        Var(x) => lookup_var(&env, &x).map(|x| x.clone()),
        Lambda(x, box body) => Ok(VClosure(env, x, body)),
        App(box rator, box rand) => {
            let fun = eval(env.clone(), rator)?;
            let arg = eval(env, rand)?;
            do_apply(fun, arg)
        }
    }
}

pub fn do_apply(rator: Value, rand: Value) -> Result<Value, Message> {
    use Neutral::*;
    use Value::*;
    dbg!(rator.clone());
    dbg!(rand.clone());
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
            println!("++vclosure");
            let fun = VClosure(env, x.clone(), body);
            dbg!(fun.clone());
            let x = freshen(&used, x);
            dbg!(x.clone());
            let body_val = do_apply(fun, VNeutral(NVar(x.clone())))?;
            dbg!(body_val.clone());
            let body_expr = read_back(cons(x.clone(), used), body_val)?;
            dbg!(body_expr.clone());
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
    println!("env= {:?}", env);
    println!("expr= {:?}", expr);
    let val = eval(env, expr)?;
    println!("v= {:?}", val);
    read_back(defs.into_iter().map(|(n, _)| n).collect(), val)
}

pub fn add_defs(env: Env<Value>, defs: List<(Name, Expr)>) -> Result<Env<Value>, Message> {
    defs.into_iter().fold(Ok(env), move |env, (x, e)| {
        let env = env?;
        let v = eval(env.clone(), e)?;
        Ok(extend(env, x, v))
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
        }
    }
    let mut names = HashMap::new();
    gather(&mut names, &e);

    fn rename(map: &HashMap<String, usize>, e: Expr) -> Expr {
        let new_name = |Name(name): Name| {
            let sz = map.len();
            let idx = map.get(&name).unwrap();
            Name(format!("{}", sz - idx - 1))
        };
        use Expr::*;
        match e {
            Var(n) => Var(new_name(n)),
            Lambda(n, box e) => Lambda(new_name(n), rename(map, e).into()),
            App(box rator, box rand) => App(rename(map, rator).into(), rename(map, rand).into()),
        }
    }

    rename(&names, e)
}

// macros

pub macro expr {
    ($id:ident) => {
        Expr::Var(Name(stringify!($id).into()))
    },
    ((lam $var:ident $expr:tt)) => {
        Expr::Lambda(Name(stringify!($var).into()), expr![$expr].into())
    },
    (($fun:ident $arg:tt)) => {
        Expr::App(expr![$fun].into(), expr![$arg].into())
    },
    (($rator:tt $rand:tt)) => {
        Expr::App(expr![$rator].into(), expr![$rand].into())
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
            def![zero <- (lam f (lam x x))],
            def![add1 <- (lam n (lam f (lam x (f ((n f) x)))))],
            def![plus <- (lam j (lam k (lam f (lam x ((j f) ((k f) x))))))],
        ];
        fn to_church(n: usize) -> Expr {
            match n {
                0 => expr![zero],
                _ => expr![(add1 {to_church(n-1)})],
            }
        }
        //        let e = expr![((plus {to_church(0)}) {to_church(1)})];
        let e = expr![(add1 zero)];
        let v = run_program(church_defs, e)?;
        println!("v= {:?}", v);
        let five = expr![(lam g (lam y (g (g (g (g (g y)))))))];
        println!("5= {:?}", alpha_norm(five.clone()));
        assert_eq!(alpha_norm(v), alpha_norm(five));
        Ok(())
    }
}
