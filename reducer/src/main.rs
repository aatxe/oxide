use std::env;
use std::fs::File;
use std::io::Read;
use std::process;

use pretty::{BoxDoc, Doc};
use syn::{Block, Expr, FnArg, GenericParam, Item, Lit, Member, Pat, Path, ReturnType, Stmt, Type};

type PP = Doc<'static, BoxDoc<'static, ()>>;

fn main() {
    let mut args = env::args();
    let _ = args.next(); // executable name

    let filename = match (args.next(), args.next()) {
        (Some(filename), None) => filename,
        _ => {
            eprintln!("Usage: dump-syntax path/to/filename.rs");
            process::exit(1);
        }
    };

    let mut file = File::open(&filename).expect("Unable to open file");

    let mut src = String::new();
    file.read_to_string(&mut src).expect("Unable to read file");

    let syntax = syn::parse_file(&src).expect("Unable to parse file");

    for item in syntax.items.into_iter() {
        if let Item::Fn(inner) = item {
            let doc: Doc<BoxDoc<()>> =
                Doc::text("(")
                // fn keyword and name
                .append(Doc::text("fn")
                        .append(Doc::space())
                        .append(Doc::text(format!("\"{}\"", inner.ident)))
                        .group()
                )
                // provenance variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                            inner.decl.generics.params.into_iter().flat_map(|param| match param {
                                GenericParam::Lifetime(lft) => Some(
                                    Doc::text(format!("\"{}\"", lft.lifetime.ident))
                                ),
                                _ => None
                            }),
                            Doc::text(";").append(Doc::space()))
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // type variables
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(Doc::text("]"))
                        .group()
                )
                // parameters
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                inner.decl.inputs.into_iter().map(|arg| match arg {
                                    FnArg::Captured(cap) =>
                                        cap.pat.to_doc()
                                            .append(Doc::space())
                                            .append(Doc::text("@:"))
                                            .append(Doc::space())
                                            .append(parenthesize(cap.ty.to_doc()))
                                            .group(),
                                    _ => Doc::nil(),
                                }),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                // return type
                .append(Doc::space())
                .append(
                    parenthesize(match inner.decl.output {
                        ReturnType::Default => Doc::text("unit_ty"),
                        ReturnType::Type(_, ty) => ty.to_doc(),
                    })
                )
                // body
                .append(Doc::space())
                .append(inner.block.to_doc())
                .append(")")
                .group();
            let mut buf = Vec::new();
            doc.render(100, &mut buf).unwrap();
            println!("{}", String::from_utf8(buf).unwrap());
        }
    }

    // println!("{:#?}", syntax);
}

fn parenthesize(doc: PP) -> PP {
    Doc::text("(")
        .append(doc.group())
        .append(Doc::text(")"))
        .group()
}

fn quote(doc: PP) -> PP {
    Doc::text("\"")
        .append(doc.group())
        .append(Doc::text("\""))
        .group()
}

trait PrettyPrint {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

trait PrettyPrintPlaceExpr {
    fn to_place_expr_doc(self) -> Doc<'static, BoxDoc<'static, ()>>;
}

impl PrettyPrint for Block {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        parenthesize(Doc::intersperse(
            self.stmts.into_iter().map(|stmt| stmt.to_doc()),
            Doc::space()
        ))
    }
}

impl PrettyPrint for Pat {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Pat::Ident(id) = self {
            return Doc::text(format!("\"{}\"", id.ident))
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Type {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Type::Reference(rf) = self {
            let lifetime = format!("{}", rf.lifetime.as_ref().unwrap().ident);
            return Doc::text("~&")
                .append(quote(Doc::text(lifetime)))
                .append(Doc::space())
                .append(rf.mutability.to_doc())
                .append(Doc::space())
                .append(parenthesize(rf.elem.to_doc()))
                .group()
        }

        if let Type::Tuple(tup) = self {
            return Doc::text("Tup")
                .append(Doc::space())
                .append(
                    Doc::text("[")
                        .append(
                            Doc::intersperse(
                                tup.elems.into_iter().map(|ty| ty.to_doc()),
                                Doc::text(";").append(Doc::space())
                            )
                        )
                        .append(Doc::text("]"))
                        .group()
                )
                .group()
        }

        if let Type::Path(path) = self {
            return path.path.to_doc()
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Stmt {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Stmt::Local(binding) = self {
            let mut pats = binding.pats;
            return Doc::text("letexp")
                .append(Doc::space())
                .append(if pats.len() == 1 {
                    pats.pop().unwrap().into_value().to_doc()
                } else {
                    panic!("we don't support multiple patterns in a binding")
                })
                .append(Doc::space())
                .append(
                    Doc::text("~:")
                        .append(match binding.ty {
                            Some((_, ty)) => parenthesize(ty.to_doc()),
                            None => panic!("types must be fully-annotated")
                        })
                        .group()
                )
                .append(Doc::space())
                .append(match binding.init {
                    Some((_, expr)) =>
                        Doc::text("(*=*)")
                        .append(Doc::space())
                        .append(parenthesize(expr.to_doc()))
                        .group(),
                    None => panic!("we don't support uninitialized bindings")
                })
                .group()
        }

        if let Stmt::Expr(expr) = self {
            return parenthesize(expr.to_doc())
        }

        if let Stmt::Semi(expr, _) = self {
            return parenthesize(expr.to_doc()
                .append(Doc::space())
                .append(Doc::text(">>"))
                .append(Doc::space())
                .append("unit"))
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrintPlaceExpr for Expr {
    fn to_place_expr_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Path(path) = self {
            return Doc::text("Var")
                .append(Doc::space())
                .append(quote(path.path.to_doc()))
        }

        self.to_doc()
    }
}

impl PrettyPrint for Expr {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Expr::Block(block) = self {
            return parenthesize(block.block.to_doc())
        }

        if let Expr::Lit(lit) = self {
            return parenthesize(lit.lit.to_doc())
        }

        if let Expr::Paren(paren) = self {
            return parenthesize(paren.expr.to_doc())
        }

        if let Expr::Reference(borrow) = self {
            return Doc::text("borrow")
                .append(Doc::space())
                .append(borrow.mutability.to_doc())
                .append(Doc::space())
                .append(parenthesize(borrow.expr.to_place_expr_doc()))
                .group()
        }

        if let expr@Expr::Path(_) = self {
            return parenthesize(
                Doc::text("move")
                    .append(Doc::space())
                    .append(parenthesize(expr.to_place_expr_doc()))
            )
        }

        if let Expr::Field(field) = self {
            return parenthesize(
                parenthesize(field.base.to_place_expr_doc())
                    .append(Doc::space())
                    .append(match field.member {
                        Member::Named(field) =>
                            Doc::text("$.$")
                            .append(Doc::space())
                            .append(Doc::text(format!("\"{}\"", field))),
                        Member::Unnamed(idx) =>
                            Doc::text("$.")
                            .append(Doc::space())
                            .append(Doc::text(format!("{}", idx.index))),
                    })
            )
        }

        if let Expr::Tuple(tup) = self {
            return parenthesize(
                Doc::text("tup")
                    .append(Doc::space())
                    .append(
                        Doc::text("[")
                            .append(Doc::intersperse(
                                tup.elems.into_iter().map(|expr| expr.to_doc()),
                                Doc::text(";").append(Doc::space())
                            ))
                            .append(Doc::text("]"))
                            .group()
                    )
            )
        }

        if let Expr::Call(call) = self {
            return Doc::text("app")
                .append(Doc::space())
                .append(parenthesize(
                    Doc::text("~@@")
                        .append(Doc::space())
                        .append(parenthesize(call.func.to_doc()))
                ))
                .append(Doc::space())
                // provenance variable arguments
                .append(
                    Doc::text("[")
                        .append(Doc::text("]"))
                        .group()
                )
                .append(Doc::space())
                // type variable arguments
                .append(
                    Doc::text("[")
                        .append(Doc::text("]"))
                        .group()
                )
                .append(Doc::space())
                // arguments
                .append(
                    Doc::text("[")
                        .append(Doc::intersperse(
                            call.args.into_iter().map(|expr| parenthesize(expr.to_doc())),
                            Doc::text(";").append(Doc::space())
                        ))
                        .append(Doc::text("]"))
                        .group()
                )
                .group()
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}

impl PrettyPrint for Path {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            self.segments.into_iter().map(|seg| Doc::text(format!("{}", seg.ident))),
            Doc::text("::")
        )
    }
}

impl PrettyPrint for Option<syn::token::Mut> {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            Some(_) => Doc::text("uniq"),
            None => Doc::text("shrd"),
        }
    }
}

impl PrettyPrint for Lit {
    fn to_doc(self) -> Doc<'static, BoxDoc<'static, ()>> {
        if let Lit::Bool(bool) = self {
            return if bool.value { Doc::text("tru") } else { Doc::text("fls") }
        }

        if let Lit::Int(int) = self {
            return parenthesize(
                Doc::text("num")
                    .append(Doc::space())
                    .append(Doc::text(format!("{}", int.value())))
            )
        }

        println!("{:#?}", self);
        Doc::text("(failwith \"unimplemented\")")
    }
}
