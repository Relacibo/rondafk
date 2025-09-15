use std::fmt::{self, Debug, Display, Formatter, Write};

use ron_edit::*;

#[must_use]
pub fn format(
    File {
        extentions,
        value,
        trailing_ws,
    }: &File,
) -> String {
    let mut out = String::new();
    let buf = &mut out;
    let c = Context {
        indent: Indent(0),
        nl: "\n",
    };

    extentions
        .iter()
        .try_for_each(|e| write!(buf, "{}", extention(e, c)))
        .inspect_err(|err| eprintln!("{err}"))
        .ok();
    if extentions.is_empty() {
        ws_lead_min(buf, value, c, &format_value)
            .inspect_err(|err| eprintln!("{err}"))
            .ok();
    } else {
        ws_lead_nl(buf, value, c, &format_value)
            .inspect_err(|err| eprintln!("{err}"))
            .ok();
        format_ws_min(buf, trailing_ws, c)
            .inspect_err(|err| eprintln!("{err}"))
            .ok();
    };
    format_ws(buf, trailing_ws, c, c, false, true, false)
        .inspect_err(|err| eprintln!("{err}"))
        .ok();
    out
}

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Indent(usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Context {
    indent: Indent,
    nl: &'static str,
}

impl Display for Indent {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:1$}", "", self.0 * 4)
    }
}

impl Context {
    #[must_use]
    fn increase(mut self) -> Self {
        self.indent.0 += 1;
        self
    }
}

fn format_value<'a>(it: &'a Value, c @ Context { nl, .. }: Context) -> impl Display + 'a {
    Disp(move |f| match it {
        lit @ (Value::Int(_)
        | Value::Float(_)
        | Value::Bool(_)
        | Value::Unit(_)
        | Value::Char(_)) => {
            write!(f, "{lit}")
        }
        Value::Str(s) => write!(
            f,
            "{}",
            if nl == "\n" {
                format!("{s}").replace("\n\r", "\n")
            } else {
                debug_assert_eq!(nl, "\n\r");
                format!("{s}").replace("\n", "\n\r")
            }
        ),
        Value::List(List(list)) => {
            write!(f, "[")?;
            format_separated(f, list, c, &format_value, false)?;
            write!(f, "]")
        }
        Value::Map(Map(fields)) => {
            write!(f, "{{")?;
            format_separated(f, fields, c, &format_map_item, false)?;
            write!(f, "}}")
        }
        Value::Tuple(Tuple { ident, fields }) => {
            option(f, ident, |ident| ws_followed_min(ident, c, &|s, _| s))?;
            write!(f, "(",)?;
            format_separated(f, fields, c, &format_value, fields.values.len() <= 1)?;
            write!(f, ")")
        }
        Value::Struct(Struct { ident, fields }) => {
            option(f, ident, |ident| ws_followed_min(ident, c, &|s, _| s))?;
            write!(f, "(")?;
            format_separated(f, fields, c, &format_named_field, false)?;
            write!(f, ")")
        }
    })
}

fn format_map_item<'a>(map_item: &'a MapItem<'_>, c: Context) -> impl Display + 'a {
    let MapItem {
        key,
        after_key,
        value,
    } = map_item;
    Disp(move |f| {
        write!(f, "{key}",)?;
        format_ws_min(f, after_key, c)?;
        write!(f, ":")?;
        ws_lead_single(f, value, c, &format_value)
    })
}

fn format_named_field<'a>(named_field: &'a NamedField<'_>, c: Context) -> impl Display + 'a {
    Disp(move |f| {
        let NamedField {
            key,
            after_key,
            value,
        } = named_field;
        write!(f, "{key}",)?;
        format_ws_min(f, after_key, c)?;
        write!(f, ":")?;
        ws_lead_single(f, value, c, &format_value)
    })
}

struct Disp<F: Fn(&mut Formatter<'_>) -> fmt::Result>(F);

impl<F: Fn(&mut Formatter<'_>) -> fmt::Result> Display for Disp<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

impl<F: Fn(&mut Formatter<'_>) -> fmt::Result> Debug for Disp<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", format!("{self}"))
    }
}

fn extention<'a>(
    WsLead {
        leading,
        content:
            Attribute {
                after_pound,
                after_exclamation,
                after_bracket,
                after_enable,
                extentions,
                after_paren,
            },
    }: &'a WsLead<Attribute>,
    c: Context,
) -> impl Display + 'a {
    Disp(move |f| {
        format_ws_min(f, leading, c)?;
        write!(f, "#")?;
        format_ws_min(f, after_pound, c)?;
        write!(f, "!")?;
        format_ws_min(f, after_exclamation, c)?;
        write!(f, "[")?;
        format_ws_min(f, after_bracket, c)?;
        write!(f, "enable")?;
        format_ws_min(f, after_enable, c)?;
        write!(f, "(")?;
        format_separated(f, extentions, c, &|&s, _| s, true)?;
        write!(f, ")")?;
        format_ws_min(f, after_paren, c)?;
        write!(f, "]")?;
        Ok(())
    })
}

fn without_trailing_nl(s: &str) -> &str {
    s.strip_suffix("\r\n").or(s.strip_suffix('\n')).unwrap_or(s)
}

fn start_with_space<'a>(s: &'a str) -> impl Display + 'a {
    Disp(move |f| {
        if s.starts_with(char::is_whitespace) {
            write!(f, "{s}")
        } else {
            write!(f, " {s}")
        }
    })
}

fn delimited_with_spaces<'a>(s: &'a str) -> impl Display + 'a {
    Disp(move |f| {
        match (
            s.starts_with(char::is_whitespace),
            s.ends_with(char::is_whitespace),
        ) {
            (true, true) => write!(f, "{s}"),
            (true, false) => write!(f, "{s} "),
            (false, true) => write!(f, " {s}"),
            (false, false) => write!(f, " {s} "),
        }
    })
}
#[test]
fn space_helpers() {
    assert_eq!(without_trailing_nl("hi\n"), "hi");
    assert_eq!(without_trailing_nl("hi\n\r\n"), "hi\n");
    assert_eq!(without_trailing_nl("hi"), "hi");
    assert_eq!(start_with_space("hi").to_string(), " hi");
    assert_eq!(start_with_space("\thi").to_string(), "\thi");
    assert_eq!(start_with_space(" hi").to_string(), " hi");
    assert_eq!(delimited_with_spaces("hi").to_string(), " hi ");
    assert_eq!(delimited_with_spaces("\thi").to_string(), "\thi ");
    assert_eq!(delimited_with_spaces(" hi").to_string(), " hi ");
    assert_eq!(delimited_with_spaces(" hi\t").to_string(), " hi\t");
}

fn ws_inner(
    f: &mut impl Write,
    ws: &Ws,
    c_after: Context,
    is_standalone: bool,
) -> Result<bool, fmt::Error> {
    let Context {
        indent: indent_after,
        nl: nl_after,
    } = c_after;
    let space = if !is_standalone {
        " "
    } else {
        Default::default()
    };
    let res = match ws {
        Ws::LineComment(c) => {
            write!(
                f,
                "{space}//{}{nl_after}{indent_after}",
                start_with_space(without_trailing_nl(c))
            )?;
            true
        }
        Ws::BlockComment(c) => {
            write!(f, "{space}/*{}*/", delimited_with_spaces(c))?;
            false
        }
        Ws::Space(_) => is_standalone,
    };
    Ok(res)
}

fn format_ws_min(
    f: &mut impl Write,
    ws: &'_ Whitespace<'_>,
    c: Context,
) -> Result<bool, fmt::Error> {
    format_ws(f, ws, c, c, false, false, false)
}

fn format_ws_single(
    f: &mut impl Write,
    ws: &Whitespace<'_>,
    c: Context,
) -> Result<bool, fmt::Error> {
    format_ws(f, ws, c, c, false, false, true)
}

fn format_ws(
    f: &mut impl Write,
    Whitespace(ws): &Whitespace,
    c @ Context { indent, nl }: Context,
    c_after @ Context {
        indent: indent_after,
        nl: nl_after,
    }: Context,
    mut is_standalone: bool,
    always_add_trailing_nl: bool,
    pad_end_with_space: bool,
) -> Result<bool, fmt::Error> {
    // Search for last non_space Ws
    let last_elem_position = ws
        .iter()
        .rev()
        .position(|elem| !matches!(elem, Ws::Space(_)));
    let after_last_elem_position = last_elem_position.map(|l| ws.len() - l).unwrap_or_default();
    let mut observed_newline = false;
    for (i, elem) in ws[..after_last_elem_position].iter().enumerate() {
        // Preserve, whether comment is standalone or preceded by non whitespace
        match elem {
            Ws::Space(s) if !observed_newline => {
                if s.contains("\n") {
                    observed_newline = true;
                }
            }
            Ws::LineComment(_) | Ws::BlockComment(_) => {
                if observed_newline && !is_standalone {
                    write!(f, "{nl}{indent}")?;
                    is_standalone = true;
                }
                let c = if i == after_last_elem_position - 1 {
                    c_after
                } else {
                    c
                };
                is_standalone = ws_inner(f, elem, c, is_standalone)?;
                observed_newline = false;
            }
            _ => {}
        }
    }

    if !is_standalone {
        if always_add_trailing_nl {
            write!(f, "{nl_after}{indent_after}")?;
        } else if pad_end_with_space {
            write!(f, " ")?;
        }
    }
    Ok(is_standalone)
}

fn format_separated<'a, T, D: Display>(
    f: &mut impl Write,
    Separated {
        values,
        trailing_comma: _,
        trailing_ws,
    }: &'a Separated<'a, T>,
    c: Context,
    format_content: &'a impl Fn(&'a T, Context) -> D,
    minimal: bool,
) -> fmt::Result {
    let increased = c.increase();
    let mut is_standalone = false;
    for (i, elem) in values.iter().enumerate() {
        let leading_always_add_trailing_newline = !minimal;
        let leading_pad_end_with_space = minimal && i != 0;
        let following_always_add_trailing_newline = i == values.len();
        let c_after = if i == values.len() { c } else { increased };
        format_ws(
            f,
            &elem.leading,
            increased,
            increased,
            is_standalone,
            leading_always_add_trailing_newline,
            leading_pad_end_with_space,
        )?;
        write!(f, "{},", format_content(&elem.content, increased),)?;
        is_standalone = format_ws(
            f,
            &elem.following,
            increased,
            c_after,
            false,
            following_always_add_trailing_newline,
            false,
        )?;
    }
    format_ws(f, trailing_ws, increased, c, is_standalone, !minimal, false)?;
    Ok(())
}

fn ws_lead_min<'a, T, D: Display>(
    f: &mut impl Write,
    WsLead { leading, content }: &'a WsLead<T>,
    c: Context,
    format_content: &'a impl Fn(&'a T, Context) -> D,
) -> fmt::Result {
    format_ws_min(f, leading, c)?;
    write!(f, "{}", format_content(content, c))
}
fn ws_followed_min<'a, T, D: Display>(
    WsFollowed { content, following }: &'a WsFollowed<T>,
    c: Context,
    format_content: &'a impl Fn(&'a T, Context) -> D,
) -> impl Display + 'a {
    Disp(move |f| {
        write!(f, "{}", format_content(content, c),)?;
        format_ws_min(f, following, c)?;
        Ok(())
    })
}
fn ws_lead_single<'a, T, D: Display>(
    f: &mut impl Write,
    WsLead { leading, content }: &'a WsLead<T>,
    c: Context,
    format_content: &'a impl Fn(&'a T, Context) -> D,
) -> fmt::Result {
    format_ws_single(f, leading, c)?;
    write!(f, "{}", format_content(content, c))?;
    Ok(())
}
fn ws_lead_nl<'a, T, D: Display>(
    f: &mut impl Write,
    WsLead { leading, content }: &'a WsLead<T>,
    c: Context,
    format_content: &'a impl Fn(&'a T, Context) -> D,
) -> fmt::Result {
    format_ws(f, leading, c, c, false, true, false)?;
    write!(f, "{}", format_content(content, c))
}
fn option<'a, T, D: Display>(
    f: &mut impl Write,
    opt: &'a Option<T>,
    format_content: impl Fn(&'a T) -> D + 'a,
) -> fmt::Result {
    if let Some(value) = opt {
        write!(f, "{}", format_content(value))
    } else {
        Ok(())
    }
}
