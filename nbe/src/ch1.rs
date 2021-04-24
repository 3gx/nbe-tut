// 1.1  Syntax
#[derive(Debug, Clone)]
pub enum Expr {
    Var(Name),
    Lambda(Name, BoxedExpr),
    App(BoxedExpr, BoxedExpr),
}
#[derive(Clone)]
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

// 1.2 Values and Runtime Environment
#[derive(Debug, Clone)]
pub enum Value {
    VClosure(Env<Value>, Name, Expr),
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

// 1.3 Evaluator
pub fn eval(env: Env<Value>, e: Expr) -> Result<Value, Message> {
    use Expr::*;
    use Value::*;
    println!("--e={:?}", e);
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
    use Value::*;
    match (rator, rand) {
        (VClosure(env, x, body), arg) => eval(extend(env, x, arg), body),
    }
}

// 1.4 Programs with Definitions

pub fn run_program(defs: List<(Name, Expr)>, expr: Expr) -> Result<Value, Message> {
    let env = add_defs(Env::new(), defs)?;
    println!("env= {:?}", env);
    eval(env, expr)
}

pub fn add_defs(env: Env<Value>, defs: List<(Name, Expr)>) -> Result<Env<Value>, Message> {
    defs.into_iter().fold(Ok(env), move |env, (x, e)| {
        let env = env?;
        let v = eval(env.clone(), e)?;
        Ok(extend(env, x, v))
    })
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
        let e = to_church(1);
        println!("e= {:?}", e);
        println!("eval(e)= {:?}", run_program(church_defs.clone(), e));
        println!("--");
        let e = expr![((plus {to_church(2)}) {to_church(3)})];
        println!("e= {:?}", e);
        let v = run_program(church_defs, e)?;
        println!("v= {:?}", v);
        match v {
            Value::VClosure(_, Name(x), body) => {
                assert_eq!(x, "f");
                let body_str = format!("{:?}", body);
                assert_eq!(body_str,
                  "Lambda(\"x\", App(App(Var(\"j\"), Var(\"f\")), App(App(Var(\"k\"), Var(\"f\")), Var(\"x\"))))");
            }
        };
        Ok(())
    }
}
