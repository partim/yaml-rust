use std::collections::BTreeMap;
use std::ops::Index;
use std::string;
use std::i64;
use std::str::FromStr;
use std::mem;
use std::vec;
use parser::*;
use scanner::{TScalarStyle, ScanError, TokenType, Marker};


/// A trait for parsing a stream of YAML documents.
///
/// Stored YAML data is called a ‘YAML character stream.’ It may contain a
/// several completely independent documents. The `Stream` trait is used
/// by `GenericYamlLoader` to parse documents from a character stream.
///
/// A YAML document consists of elements that are either scalars, sequences,
/// or mappings. The trait has a method for each of these kinds to create a
/// new element. All elements are eventually represented by the `Self::Item``
/// associated type. Sequences and mappings are represented by their own types
/// and traits while they are being constructed. Once they are finished, they
/// too need to be converted into `Self::Item`s.
///
/// Once a document is finished, the method `create_document()` is called to
/// give the `Self::Item` representing all elements of the document to the
/// stream to process it.
pub trait Stream {
    /// The type for all items of the document.
    type Item: Clone;

    /// The type used for building sequences.
    type Sequence: Sequence<Item=Self::Item>;

    /// The type used for building mappings.
    type Mapping: Mapping<Item=Self::Item>;

    /// Creates a new scalar item.
    fn create_scalar(&self, value: &str, style: TScalarStyle,
                     tag: &Option<TokenType>, mark: Marker) -> Self::Item;

    /// Creates a bad value item.
    ///
    /// Such values are created for invalid type conversion and when
    /// accessing non-existent aliases.
    fn create_bad_value(&self) -> Self::Item;

    /// Creates a new sequence builder.
    fn create_sequence(&self, mark: Marker) -> Self::Sequence;

    /// Creates a new mapping builder.
    fn create_mapping(&self, mark: Marker) -> Self::Mapping;

    /// Creates and consumes a document from an item.
    fn create_document(&mut self, item: Self::Item);
}


/// A trait representing a sequence being parsed.
///
/// Each element of the sequence is parsed into a value of the `Self::Item`
/// associated type and then added via the `push()` method. Once all elements
/// are added, the sequence is converted into an item itself through the
/// `finalize()` method.
pub trait Sequence: Clone {
    /// The item type used by documents containing this sequence.
    type Item: Clone;

    /// Adds a new element ot the sequence.
    fn push(&mut self, item: Self::Item);

    /// Converts the sequence into an item for further processing.
    fn finalize(self) -> Self::Item;
}

/// A trait representing a mapping being parsed.
///
/// Key and value of the each element of the mapping
/// are parsed into values of the `Self::Item` associated type and then added
/// via the `insert()` method. Once all elements have been added, the mapping
/// is converted into an item through the `finalize()` method.
pub trait Mapping: Clone {
    /// The item type used by documents containing this sequence.
    type Item: Clone;

    /// Adds a new element with the given key and value.
    fn insert(&mut self, key: Self::Item, value: Self::Item);

    /// Converts the mapping into an item for further processing.
    fn finalize(self) -> Self::Item;
}


/// A YAML node is stored as this `Yaml` enumeration, which provides an easy way to
/// access your YAML document.
///
/// # Examples
///
/// ```
/// use yaml_rust::Yaml;
/// let foo = Yaml::from_str("-123"); // convert the string to the appropriate YAML type
/// assert_eq!(foo.as_i64().unwrap(), -123);
///
/// // iterate over an Array
/// let vec = Yaml::Array(vec![Yaml::Integer(1), Yaml::Integer(2)]);
/// for v in vec.as_vec().unwrap() {
///     assert!(v.as_i64().is_some());
/// }
/// ```
#[derive(Clone, PartialEq, PartialOrd, Debug, Eq, Ord, Hash)]
pub enum Yaml {
    /// Float types are stored as String and parsed on demand.
    /// Note that f64 does NOT implement Eq trait and can NOT be stored in BTreeMap.
    Real(string::String),
    /// YAML int is stored as i64.
    Integer(i64),
    /// YAML scalar.
    String(string::String),
    /// YAML bool, e.g. `true` or `false`.
    Boolean(bool),
    /// YAML array, can be accessed as a `Vec`.
    Array(self::Array),
    /// YAML hash, can be accessed as a `BTreeMap`.
    ///
    /// If the order of keys is meaningful, enable the `preserve_order` feature to
    /// store hashes as a `LinkedHashMap` intead of `BTreeMap`. When using a
    /// `LinkedHashMap`, the itertion order will match the order of insertion into
    /// the map.
    ///
    /// ```toml
    /// yaml-rust = { version = "*", features = ["preserve_order"] }
    /// ```
    Hash(self::Hash),
    /// Alias, not fully supported yet.
    Alias(usize),
    /// YAML null, e.g. `null` or `~`.
    Null,
    /// Accessing a nonexistent node via the Index trait returns `BadValue`. This
    /// simplifies error handling in the calling code. Invalid type conversion also
    /// returns `BadValue`.
    BadValue,
}


pub struct YamlLoader(Vec<Yaml>);

impl YamlLoader {
    pub fn new() -> Self {
        YamlLoader(Vec::new())
    }

    pub fn load_from_str(source: &str) -> Result<Vec<Yaml>, ScanError> {
        GenericYamlLoader::load_from_str(source, YamlLoader::new())
                         .map(|loader| loader.0)
    }
}


impl Stream for YamlLoader {
    type Item = Yaml;
    type Sequence = Array;
    type Mapping = Hash;

    fn create_scalar(&self, v: &str, style: TScalarStyle,
                     tag: &Option<TokenType>, _mark: Marker) -> Self::Item {
        if style != TScalarStyle::Plain {
            Yaml::String(v.into())
        } else if let Some(TokenType::Tag(ref handle, ref suffix)) = *tag {
            // XXX tag:yaml.org,2002:
            if handle == "!!" {
                match suffix.as_ref() {
                    "bool" => {
                        // "true" or "false"
                        match v.parse::<bool>() {
                            Err(_) => Yaml::BadValue,
                            Ok(v) => Yaml::Boolean(v)
                        }
                    },
                    "int" => {
                        match v.parse::<i64>() {
                            Err(_) => Yaml::BadValue,
                            Ok(v) => Yaml::Integer(v)
                        }
                    },
                    "float" => {
                        match v.parse::<f64>() {
                            Err(_) => Yaml::BadValue,
                            Ok(_) => Yaml::Real(v.into())
                        }
                    },
                    "null" => {
                        match v.as_ref() {
                            "~" | "null" => Yaml::Null,
                            _ => Yaml::BadValue,
                        }
                    }
                    _  => Yaml::String(v.into()),
                }
            } else {
                Yaml::String(v.into())
            }
        } else {
            // Datatype is not specified, or unrecognized
            Yaml::from_str(v.as_ref())
        }
    }

    fn create_bad_value(&self) -> Self::Item {
        Yaml::BadValue
    }

    fn create_sequence(&self, _mark: Marker) -> Self::Sequence {
        Vec::new()
    }

    fn create_mapping(&self, _mark: Marker) -> Self::Mapping {
        Hash::new()
    }

    fn create_document(&mut self, item: Yaml) {
        self.0.push(item)
    }
}


pub type Array = Vec<Yaml>;

impl Sequence for Array {
    type Item = Yaml;

    fn push(&mut self, item: Yaml) {
        self.push(item)
    }

    fn finalize(self) -> Yaml {
        Yaml::Array(self)
    }
}


#[cfg(not(feature = "preserve_order"))]
pub type Hash = BTreeMap<Yaml, Yaml>;
#[cfg(feature = "preserve_order")]
pub type Hash = ::linked_hash_map::LinkedHashMap<Yaml, Yaml>;

impl Mapping for Hash {
    type Item = Yaml;

    fn insert(&mut self, key: Yaml, value: Yaml) {
        self.insert(key, value);
    }

    fn finalize(self) -> Yaml {
        Yaml::Hash(self)
    }
}


enum Node<D: Stream> {
    Scalar(D::Item),
    Array(D::Sequence),
    Hash(D::Mapping),
    BadValue(D::Item),
}

impl<D: Stream> Node<D> {
    pub fn is_badvalue(&self) -> bool {
        match *self {
            Node::BadValue(_) => true,
            _ => false
        }
    }

    fn into_item(self) -> D::Item {
        match self {
            Node::Scalar(item) => item,
            Node::Array(item) => item.finalize(),
            Node::Hash(item) => item.finalize(),
            Node::BadValue(item) => item,
        }
    }
}

impl<D: Stream> Clone for Node<D> {
    fn clone(&self) -> Self {
        match *self {
            Node::Scalar(ref item) => Node::Scalar(item.clone()),
            Node::Array(ref item) => Node::Array(item.clone()),
            Node::Hash(ref item) => Node::Hash(item.clone()),
            Node::BadValue(ref item) => Node::BadValue(item.clone()),
        }
    }
}

pub struct GenericYamlLoader<D: Stream> {
    builder: D,
    // states
    // (current node, anchor_id) tuple
    doc_stack: Vec<(Node<D>, usize)>,
    key_stack: Vec<Node<D>>,
    anchor_map: BTreeMap<usize, Node<D>>,
}

impl<D: Stream> MarkedEventReceiver for GenericYamlLoader<D> {
    fn on_event(&mut self, ev: &Event, mark: Marker) {
        // println!("EV {:?}", ev);
        match *ev {
            Event::DocumentStart => {
                // do nothing
            },
            Event::DocumentEnd => {
                let node = match self.doc_stack.len() {
                    // empty document
                    0 => Node::BadValue(self.builder.create_bad_value()),
                    1 => self.doc_stack.pop().unwrap().0,
                    _ => unreachable!()
                };
                self.builder.create_document(node.into_item());
            },
            Event::SequenceStart(aid) => {
                self.doc_stack.push(
                    (Node::Array(self.builder.create_sequence(mark)),
                     aid));
            },
            Event::SequenceEnd => {
                let node = self.doc_stack.pop().unwrap();
                self.insert_new_node(node);
            },
            Event::MappingStart(aid) => {
                self.doc_stack.push(
                    (Node::Hash(self.builder.create_mapping(mark)), aid));
                self.key_stack.push(
                    Node::BadValue(self.builder.create_bad_value()));
            },
            Event::MappingEnd => {
                self.key_stack.pop().unwrap();
                let node = self.doc_stack.pop().unwrap();
                self.insert_new_node(node);
            },
            Event::Scalar(ref v, style, aid, ref tag) => {
                let item = self.builder.create_scalar(v, style, tag, mark);
                self.insert_new_node((Node::Scalar(item), aid));
            },
            Event::Alias(id) => {
                let n = match self.anchor_map.get(&id) {
                    Some(v) => v.clone(),
                    None => Node::BadValue(self.builder.create_bad_value()),
                };
                self.insert_new_node((n, 0));
            }
            _ => { /* ignore */ }
        }
        // println!("DOC {:?}", self.doc_stack);
    }
}

impl<D: Stream> GenericYamlLoader<D> {
    fn insert_new_node(&mut self, node: (Node<D>, usize)) {
        // valid anchor id starts from 1
        if node.1 > 0 {
            self.anchor_map.insert(node.1, node.0.clone());
        }
        if self.doc_stack.is_empty() {
            self.doc_stack.push(node);
        } else {
            let parent = self.doc_stack.last_mut().unwrap();
            match *parent {
                (Node::Array(ref mut v), _) => v.push(node.0.into_item()),
                (Node::Hash(ref mut h), _) => {
                    let mut cur_key = self.key_stack.last_mut().unwrap();
                    // current node is a key
                    if cur_key.is_badvalue() {
                        *cur_key = node.0;
                    // current node is a value
                    } else {
                        let mut newkey = Node::BadValue(
                                            self.builder.create_bad_value());
                        mem::swap(&mut newkey, cur_key);
                        h.insert(newkey.into_item(), node.0.into_item());
                    }
                },
                _ => unreachable!(),
            }
        }
    }

    pub fn load_from_str(source: &str, builder: D)
                         -> Result<D, ScanError>{
        let mut loader = GenericYamlLoader {
            builder: builder,
            doc_stack: Vec::new(),
            key_stack: Vec::new(),
            anchor_map: BTreeMap::new(),
        };
        let mut parser = Parser::new(source.chars());
        try!(parser.load(&mut loader, true));
        Ok(loader.builder)
    }
}


macro_rules! define_as (
    ($name:ident, $t:ident, $yt:ident) => (
pub fn $name(&self) -> Option<$t> {
    match *self {
        Yaml::$yt(v) => Some(v),
        _ => None
    }
}
    );
);

macro_rules! define_as_ref (
    ($name:ident, $t:ty, $yt:ident) => (
pub fn $name(&self) -> Option<$t> {
    match *self {
        Yaml::$yt(ref v) => Some(v),
        _ => None
    }
}
    );
);

macro_rules! define_into (
    ($name:ident, $t:ty, $yt:ident) => (
pub fn $name(self) -> Option<$t> {
    match self {
        Yaml::$yt(v) => Some(v),
        _ => None
    }
}
    );
);

impl Yaml {
    define_as!(as_bool, bool, Boolean);
    define_as!(as_i64, i64, Integer);

    define_as_ref!(as_str, &str, String);
    define_as_ref!(as_hash, &Hash, Hash);
    define_as_ref!(as_vec, &Array, Array);

    define_into!(into_bool, bool, Boolean);
    define_into!(into_i64, i64, Integer);
    define_into!(into_string, String, String);
    define_into!(into_hash, Hash, Hash);
    define_into!(into_vec, Array, Array);

    pub fn is_null(&self) -> bool {
        match *self {
            Yaml::Null => true,
            _ => false
        }
    }

    pub fn is_badvalue(&self) -> bool {
        match *self {
            Yaml::BadValue => true,
            _ => false
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match *self {
            Yaml::Real(ref v) => {
                v.parse::<f64>().ok()
            },
            _ => None
        }
    }

    pub fn into_f64(self) -> Option<f64> {
        match self {
            Yaml::Real(v) => {
                v.parse::<f64>().ok()
            },
            _ => None
        }
    }
}

#[cfg_attr(feature="clippy", allow(should_implement_trait))]
impl Yaml {
    // Not implementing FromStr because there is no possibility of Error.
    // This function falls back to Yaml::String if nothing else matches.
    pub fn from_str(v: &str) -> Yaml {
        if v.starts_with("0x") {
            let n = i64::from_str_radix(&v[2..], 16);
            if n.is_ok() {
                return Yaml::Integer(n.unwrap());
            }
        }
        if v.starts_with("0o") {
            let n = i64::from_str_radix(&v[2..], 8);
            if n.is_ok() {
                return Yaml::Integer(n.unwrap());
            }
        }
        if v.starts_with('+') && v[1..].parse::<i64>().is_ok() {
            return Yaml::Integer(v[1..].parse::<i64>().unwrap());
        }
        match v {
            "~" | "null" => Yaml::Null,
            "true" => Yaml::Boolean(true),
            "false" => Yaml::Boolean(false),
            _ if v.parse::<i64>().is_ok() => Yaml::Integer(v.parse::<i64>().unwrap()),
            // try parsing as f64
            _ if v.parse::<f64>().is_ok() => Yaml::Real(v.to_owned()),
            _ => Yaml::String(v.to_owned())
        }
    }
}

static BAD_VALUE: Yaml = Yaml::BadValue;
impl<'a> Index<&'a str> for Yaml {
    type Output = Yaml;

    fn index(&self, idx: &'a str) -> &Yaml {
        let key = Yaml::String(idx.to_owned());
        match self.as_hash() {
            Some(h) => h.get(&key).unwrap_or(&BAD_VALUE),
            None => &BAD_VALUE
        }
    }
}

impl Index<usize> for Yaml {
    type Output = Yaml;

    fn index(&self, idx: usize) -> &Yaml {
        match self.as_vec() {
            Some(v) => v.get(idx).unwrap_or(&BAD_VALUE),
            None => &BAD_VALUE
        }
    }
}

impl IntoIterator for Yaml {
    type Item = Yaml;
    type IntoIter = YamlIter;

    fn into_iter(self) -> Self::IntoIter {
        YamlIter {
            yaml: self.into_vec()
                .unwrap_or_else(Vec::new).into_iter()
        }
    }
}

pub struct YamlIter {
    yaml: vec::IntoIter<Yaml>,
}

impl Iterator for YamlIter {
    type Item = Yaml;

    fn next(&mut self) -> Option<Yaml> {
        self.yaml.next()
    }
}

#[cfg(test)]
mod test {
    use yaml::*;
    #[test]
    fn test_coerce() {
        let s = "---
a: 1
b: 2.2
c: [1, 2]
";
        let out = YamlLoader::load_from_str(&s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a"].as_i64().unwrap(), 1i64);
        assert_eq!(doc["b"].as_f64().unwrap(), 2.2f64);
        assert_eq!(doc["c"][1].as_i64().unwrap(), 2i64);
        assert!(doc["d"][0].is_badvalue());
    }

    #[test]
    fn test_empty_doc() {
        let s: String = "".to_owned();
        YamlLoader::load_from_str(&s).unwrap();
        let s: String = "---".to_owned();
        assert_eq!(YamlLoader::load_from_str(&s).unwrap()[0], Yaml::Null);
    }

    #[test]
    fn test_parser() {
        let s: String = "
# comment
a0 bb: val
a1:
    b1: 4
    b2: d
a2: 4 # i'm comment
a3: [1, 2, 3]
a4:
    - - a1
      - a2
    - 2
a5: 'single_quoted'
a6: \"double_quoted\"
a7: 你好
".to_owned();
        let out = YamlLoader::load_from_str(&s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a7"].as_str().unwrap(), "你好");
    }

    #[test]
    fn test_multi_doc() {
        let s =
"
'a scalar'
---
'a scalar'
---
'a scalar'
";
        let out = YamlLoader::load_from_str(&s).unwrap();
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn test_anchor() {
        let s =
"
a1: &DEFAULT
    b1: 4
    b2: d
a2: *DEFAULT
";
        let out = YamlLoader::load_from_str(&s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a2"]["b1"].as_i64().unwrap(), 4);
    }

    #[test]
    fn test_bad_anchor() {
        let s =
"
a1: &DEFAULT
    b1: 4
    b2: *DEFAULT
";
        let out = YamlLoader::load_from_str(&s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a1"]["b2"], Yaml::BadValue);

    }

    #[test]
    fn test_github_27() {
        // https://github.com/chyh1990/yaml-rust/issues/27
        let s = "&a";
        let out = YamlLoader::load_from_str(&s).unwrap();
        let doc = &out[0];
        assert_eq!(doc.as_str().unwrap(), "");
    }

    #[test]
    fn test_plain_datatype() {
        let s =
"
- 'string'
- \"string\"
- string
- 123
- -321
- 1.23
- -1e4
- ~
- null
- true
- false
- !!str 0
- !!int 100
- !!float 2
- !!null ~
- !!bool true
- !!bool false
- 0xFF
# bad values
- !!int string
- !!float string
- !!bool null
- !!null val
- 0o77
- [ 0xF, 0xF ]
- +12345
- [ true, false ]
";
        let out = YamlLoader::load_from_str(&s).unwrap();
        let doc = &out[0];

        assert_eq!(doc[0].as_str().unwrap(), "string");
        assert_eq!(doc[1].as_str().unwrap(), "string");
        assert_eq!(doc[2].as_str().unwrap(), "string");
        assert_eq!(doc[3].as_i64().unwrap(), 123);
        assert_eq!(doc[4].as_i64().unwrap(), -321);
        assert_eq!(doc[5].as_f64().unwrap(), 1.23);
        assert_eq!(doc[6].as_f64().unwrap(), -1e4);
        assert!(doc[7].is_null());
        assert!(doc[8].is_null());
        assert_eq!(doc[9].as_bool().unwrap(), true);
        assert_eq!(doc[10].as_bool().unwrap(), false);
        assert_eq!(doc[11].as_str().unwrap(), "0");
        assert_eq!(doc[12].as_i64().unwrap(), 100);
        assert_eq!(doc[13].as_f64().unwrap(), 2.0);
        assert!(doc[14].is_null());
        assert_eq!(doc[15].as_bool().unwrap(), true);
        assert_eq!(doc[16].as_bool().unwrap(), false);
        assert_eq!(doc[17].as_i64().unwrap(), 255);
        assert!(doc[18].is_badvalue());
        assert!(doc[19].is_badvalue());
        assert!(doc[20].is_badvalue());
        assert!(doc[21].is_badvalue());
        assert_eq!(doc[22].as_i64().unwrap(), 63);
        assert_eq!(doc[23][0].as_i64().unwrap(), 15);
        assert_eq!(doc[23][1].as_i64().unwrap(), 15);
        assert_eq!(doc[24].as_i64().unwrap(), 12345);
        assert!(doc[25][0].as_bool().unwrap());
        assert!(!doc[25][1].as_bool().unwrap());
    }

    #[test]
    fn test_bad_hypen() {
        // See: https://github.com/chyh1990/yaml-rust/issues/23
        let s = "{-";
        assert!(YamlLoader::load_from_str(&s).is_err());
    }

    #[test]
    fn test_bad_docstart() {
        assert!(YamlLoader::load_from_str("---This used to cause an infinite loop").is_ok());
        assert_eq!(YamlLoader::load_from_str("----"), Ok(vec![Yaml::String(String::from("----"))]));
        assert_eq!(YamlLoader::load_from_str("--- #here goes a comment"), Ok(vec![Yaml::Null]));
        assert_eq!(YamlLoader::load_from_str("---- #here goes a comment"), Ok(vec![Yaml::String(String::from("----"))]));
    }

    #[test]
    fn test_plain_datatype_with_into_methods() {
        let s =
"
- 'string'
- \"string\"
- string
- 123
- -321
- 1.23
- -1e4
- true
- false
- !!str 0
- !!int 100
- !!float 2
- !!bool true
- !!bool false
- 0xFF
- 0o77
- +12345
";
        let mut out = YamlLoader::load_from_str(&s).unwrap().into_iter();
        let mut doc = out.next().unwrap().into_iter();

        assert_eq!(doc.next().unwrap().into_string().unwrap(), "string");
        assert_eq!(doc.next().unwrap().into_string().unwrap(), "string");
        assert_eq!(doc.next().unwrap().into_string().unwrap(), "string");
        assert_eq!(doc.next().unwrap().into_i64().unwrap(), 123);
        assert_eq!(doc.next().unwrap().into_i64().unwrap(), -321);
        assert_eq!(doc.next().unwrap().into_f64().unwrap(), 1.23);
        assert_eq!(doc.next().unwrap().into_f64().unwrap(), -1e4);
        assert_eq!(doc.next().unwrap().into_bool().unwrap(), true);
        assert_eq!(doc.next().unwrap().into_bool().unwrap(), false);
        assert_eq!(doc.next().unwrap().into_string().unwrap(), "0");
        assert_eq!(doc.next().unwrap().into_i64().unwrap(), 100);
        assert_eq!(doc.next().unwrap().into_f64().unwrap(), 2.0);
        assert_eq!(doc.next().unwrap().into_bool().unwrap(), true);
        assert_eq!(doc.next().unwrap().into_bool().unwrap(), false);
        assert_eq!(doc.next().unwrap().into_i64().unwrap(), 255);
        assert_eq!(doc.next().unwrap().into_i64().unwrap(), 63);
        assert_eq!(doc.next().unwrap().into_i64().unwrap(), 12345);
    }
}
