use std::{
    borrow::Cow,
    fmt::{self, Debug, Display, Formatter, Write},
};

use ron_edit::*;

pub fn format(
    f: &mut impl Write,
    File {
        extentions: extensions,
        value,
        trailing_ws,
    }: &File,
) -> Result<(), Error> {
    let c = Context {
        indent: Indent(0),
        nl: "\n",
    };

    if extensions.is_empty() {
        ws_lead_min(f, value, c)?;
    } else {
        for extension in extensions {
            format_extension(f, extension, c)?;
        }
        ws_lead_nl(f, value, c)?;
        format_ws_min(f, trailing_ws, c)?;
    };
    format_ws(f, trailing_ws, c, c, false, true, false)?;
    Ok(())
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
    fn increase(mut self) -> Self {
        self.indent.0 += 1;
        self
    }
}

trait Formattable {
    fn format<W: Write>(&self, f: &mut W, c: Context) -> fmt::Result;
}

impl Formattable for Value<'_> {
    fn format<'a, W: Write>(&self, f: &mut W, c @ Context { nl, .. }: Context) -> fmt::Result {
        match self {
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
                format_separated(f, list, c, false)?;
                write!(f, "]")
            }
            Value::Map(Map(fields)) => {
                write!(f, "{{")?;
                format_separated(f, fields, c, false)?;
                write!(f, "}}")
            }
            Value::Tuple(Tuple { ident, fields }) => {
                if let Some(ident) = ident {
                    ident.format(f, c)?;
                };
                write!(f, "(",)?;
                format_separated(f, fields, c, fields.values.len() <= 1)?;
                write!(f, ")")
            }
            Value::Struct(Struct { ident, fields }) => {
                if let Some(ident) = ident {
                    ident.format(f, c)?;
                };
                write!(f, "(")?;
                format_separated(f, fields, c, false)?;
                write!(f, ")")
            }
        }
    }
}

impl Formattable for &str {
    fn format<W: Write>(&self, f: &mut W, _: Context) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl<F: Formattable> Formattable for WsFollowed<'_, F> {
    fn format<W: Write>(&self, f: &mut W, c: Context) -> fmt::Result {
        ws_followed_min(f, self, c)
    }
}

impl Formattable for MapItem<'_> {
    fn format<W: Write>(&self, f: &mut W, c: Context) -> fmt::Result {
        let MapItem {
            key,
            after_key,
            value,
        } = self;
        write!(f, "{key}",)?;
        format_ws_min(f, after_key, c)?;
        write!(f, ":")?;
        ws_lead_single(f, value, c)
    }
}
impl Formattable for NamedField<'_> {
    fn format<W: Write>(&self, f: &mut W, c: Context) -> fmt::Result {
        let NamedField {
            key,
            after_key,
            value,
        } = self;
        write!(f, "{key}",)?;
        format_ws_min(f, after_key, c)?;
        write!(f, ":")?;
        ws_lead_single(f, value, c)
    }
}

fn format_extension(
    f: &mut impl Write,
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
    }: &WsLead<Attribute>,
    c: Context,
) -> fmt::Result {
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
    format_separated(f, extentions, c, true)?;
    write!(f, ")")?;
    format_ws_min(f, after_paren, c)?;
    write!(f, "]")?;
    Ok(())
}

fn without_trailing_nl(s: &str) -> &str {
    s.strip_suffix("\r\n").or(s.strip_suffix('\n')).unwrap_or(s)
}

fn start_with_space(s: &str) -> Cow<'_, str> {
    if s.starts_with(char::is_whitespace) {
        s.into()
    } else {
        format!(" {s}").into()
    }
}

fn delimited_with_spaces(s: &str) -> Cow<'_, str> {
    match (
        s.starts_with(char::is_whitespace),
        s.ends_with(char::is_whitespace),
    ) {
        (true, true) => s.into(),
        (true, false) => format!("{s} ").into(),
        (false, true) => format!(" {s}").into(),
        (false, false) => format!(" {s} ").into(),
    }
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

fn format_separated<'a, F: Formattable>(
    f: &mut impl Write,
    Separated {
        values,
        trailing_comma: _,
        trailing_ws,
    }: &'a Separated<'a, F>,
    c: Context,
    minimal: bool,
) -> fmt::Result {
    let increased = c.increase();
    let mut is_standalone = false;
    for (i, elem) in values.iter().enumerate() {
        let WsWrapped {
            leading,
            content,
            following,
        } = &elem;
        let leading_always_add_trailing_newline = !minimal;
        let leading_pad_end_with_space = minimal && i != 0;
        let following_always_add_trailing_newline = i == values.len();
        let c_after = if i == values.len() { c } else { increased };
        format_ws(
            f,
            leading,
            increased,
            increased,
            is_standalone,
            leading_always_add_trailing_newline,
            leading_pad_end_with_space,
        )?;
        content.format(f, increased)?;
        write!(f, ",")?;
        is_standalone = format_ws(
            f,
            following,
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

fn ws_lead_min<F: Formattable>(
    f: &mut impl Write,
    WsLead { leading, content }: &WsLead<F>,
    c: Context,
) -> fmt::Result {
    format_ws_min(f, leading, c)?;
    content.format(f, c)?;
    write!(f, ",")
}
fn ws_followed_min<F: Formattable>(
    f: &mut impl Write,
    WsFollowed { content, following }: &WsFollowed<F>,
    c: Context,
) -> fmt::Result {
    content.format(f, c)?;
    format_ws_min(f, following, c)?;
    Ok(())
}
fn ws_lead_single<F: Formattable>(
    f: &mut impl Write,
    WsLead { leading, content }: &WsLead<F>,
    c: Context,
) -> fmt::Result {
    format_ws_single(f, leading, c)?;
    content.format(f, c)
}
fn ws_lead_nl<F: Formattable>(
    f: &mut impl Write,
    WsLead { leading, content }: &WsLead<F>,
    c: Context,
) -> fmt::Result {
    format_ws(f, leading, c, c, false, true, false)?;
    content.format(f, c)
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Formatting failed: {}", .0)]
    FormattingFailed(#[from] fmt::Error),
}

#[cfg(test)]
mod test {
    use crate::without_trailing_nl;

    #[test]
    fn space_helpers() {
        assert_eq!(without_trailing_nl("hi\n"), "hi");
        assert_eq!(without_trailing_nl("hi\n\r\n"), "hi\n");
        assert_eq!(without_trailing_nl("hi"), "hi");
        // assert_eq!(start_with_space("hi").to_string(), " hi");
        // assert_eq!(start_with_space("\thi").to_string(), "\thi");
        // assert_eq!(start_with_space(" hi").to_string(), " hi");
        // assert_eq!(delimited_with_spaces("hi").to_string(), " hi ");
        // assert_eq!(delimited_with_spaces("\thi").to_string(), "\thi ");
        // assert_eq!(delimited_with_spaces(" hi").to_string(), " hi ");
        // assert_eq!(delimited_with_spaces(" hi\t").to_string(), " hi\t");
    }
}
