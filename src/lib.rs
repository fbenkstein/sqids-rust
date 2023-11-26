#![warn(missing_docs)]
#![allow(clippy::tabs_in_doc_comments)]
#![doc = include_str!("../README.md")]

// Make the link to the LICENSE in README.md work.
#[cfg(doc)]
#[doc = include_str!("../LICENSE")]
///
/// ---
/// **Note**: This is the crate's license and not an actual item.
pub const LICENSE: () = ();

use std::{cell::Cell, cmp::min, collections::HashSet, result};

use derive_builder::Builder;
use thiserror::Error;

/// sqids Error type.
#[derive(Error, Debug, Eq, PartialEq)]
pub enum Error {
	/// Alphabet cannot contain multibyte characters
	///
	/// ```
	/// # use sqids::{Sqids, Error};
	/// let error = Sqids::builder().alphabet("☃️🦀🔥".chars().collect()).build().unwrap_err();
	/// assert_eq!(error, Error::AlphabetMultibyteCharacters);
	/// ```
	#[error("Alphabet cannot contain multibyte characters")]
	AlphabetMultibyteCharacters,
	/// Alphabet length must be at least 3
	///
	/// ```
	/// # use sqids::{Sqids, Error};
	/// let error = Sqids::builder().alphabet("ab".chars().collect()).build().unwrap_err();
	/// assert_eq!(error, Error::AlphabetLength);
	/// ```
	#[error("Alphabet length must be at least 3")]
	AlphabetLength,
	/// Alphabet must contain unique characters
	///
	/// ```
	/// # use sqids::{Sqids, Error};
	/// let error = Sqids::builder().alphabet("aba".chars().collect()).build().unwrap_err();
	/// assert_eq!(error, Error::AlphabetUniqueCharacters);
	/// ```
	#[error("Alphabet must contain unique characters")]
	AlphabetUniqueCharacters,
	/// Reached max attempts to re-generate the ID
	///
	/// ```
	/// # use sqids::{Sqids, Error};
	/// let sqids = Sqids::builder()
	/// 	.alphabet("abc".chars().collect())
	/// 	.min_length(3)
	/// 	.blocklist(["aac".to_string(), "bba".to_string(), "ccb".to_string()].into())
	/// 	.build()
	/// 	.unwrap();
	/// let error = sqids.encode(&[1]).unwrap_err();
	/// assert_eq!(error, Error::BlocklistMaxAttempts);
	/// ```
	#[error("Reached max attempts to re-generate the ID")]
	BlocklistMaxAttempts,
}

/// type alias for Result<T, Error>
pub type Result<T> = result::Result<T, Error>;

/// The default alphabet used when none is given when creating a [Sqids].
pub const DEFAULT_ALPHABET: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

/// Returns the default blocklist when none is given when creating a [Sqids].
pub fn default_blocklist() -> HashSet<String> {
	serde_json::from_str(include_str!("blocklist.json")).unwrap()
}

/// Options for creating a [Sqids].
#[derive(Debug)]
pub struct Options {
	/// The [Sqids] alphabet.
	pub alphabet: String,
	/// The minimum length of a sqid.
	pub min_length: u8,
	/// Blocklist. When creating a sqid [Sqids] will try to avoid generating a string that begins
	/// with one of these.
	pub blocklist: HashSet<String>,
}

impl Options {
	/// Create an [Options] object.
	pub fn new(
		alphabet: Option<String>,
		min_length: Option<u8>,
		blocklist: Option<HashSet<String>>,
	) -> Self {
		let mut options = Options::default();

		if let Some(alphabet) = alphabet {
			options.alphabet = alphabet;
		}
		if let Some(min_length) = min_length {
			options.min_length = min_length;
		}
		if let Some(blocklist) = blocklist {
			options.blocklist = blocklist;
		}

		options
	}
}

impl Default for Options {
	fn default() -> Self {
		Options {
			alphabet: DEFAULT_ALPHABET.to_string(),
			min_length: 0,
			blocklist: default_blocklist(),
		}
	}
}

/// A generator for sqids.
#[derive(Debug, Builder)]
#[builder(build_fn(skip, error = "Error"), pattern = "owned")]
pub struct Sqids {
	/// The alphabet that is being used when generating sqids.
	#[builder(field(type = "Option<String>"), setter(strip_option))]
	alphabet: Vec<u8>,
	/// The minimum length of a sqid.
	min_length: u8,
	/// Blocklist. When creating a sqid strings that begins
	/// with one of these will be avoided.
	#[builder(field(type = "Option<HashSet<String>>"), setter(strip_option))]
	blocklist: HashSet<Vec<u8>>,
}

impl Default for Sqids {
	fn default() -> Self {
		Self::builder().build().unwrap()
	}
}

impl SqidsBuilder {
	/// Create a [SqidsBuilder].
	pub fn new() -> Self {
		Self::default()
	}

	/// Build a [Sqids] object.
	pub fn build(self) -> Result<Sqids> {
		let alphabet: String = self.alphabet.unwrap_or_else(|| DEFAULT_ALPHABET.to_string());

		for c in alphabet.chars() {
			if c.len_utf8() > 1 {
				return Err(Error::AlphabetMultibyteCharacters);
			}
		}

		if alphabet.len() < 3 {
			return Err(Error::AlphabetLength);
		}

		let unique_chars: HashSet<char> = alphabet.chars().collect();
		if unique_chars.len() != alphabet.len() {
			return Err(Error::AlphabetUniqueCharacters);
		}

		let lowercase_alphabet: Vec<char> =
			alphabet.chars().map(|c| c.to_ascii_lowercase()).collect();
		// Lowercase all words, remove words that contain characters not in the alphabet since these
		// can never match and then make words into byte vectors.
		let blocklist = self
			.blocklist
			.unwrap_or_else(default_blocklist)
			.iter()
			.filter_map(|word| {
				let word = word.to_lowercase();
				if word.len() >= 3 && word.chars().all(|c| lowercase_alphabet.contains(&c)) {
					Some(word.into_bytes())
				} else {
					None
				}
			})
			.collect();

		let mut alphabet = alphabet.into_bytes();
		Sqids::shuffle(&mut alphabet);
		let min_length = self.min_length.unwrap_or(0);

		Ok(Sqids { alphabet, min_length, blocklist })
	}
}

impl Sqids {
	/// Create a [Sqids] from [Options].
	pub fn new(options: Option<Options>) -> Result<Self> {
		let options = options.unwrap_or_default();
		Self::builder()
			.min_length(options.min_length)
			.alphabet(options.alphabet.chars().collect())
			.blocklist(options.blocklist)
			.build()
	}

	/// Create a [SqidsBuilder].
	pub fn builder() -> SqidsBuilder {
		SqidsBuilder::default()
	}

	/// Generate a sqid from a slice of numbers.
	///
	/// When an sqid is generated it is checked against the [SqidsBuilder::blocklist]. When a
	/// blocked word is encountered another attempt is made by shifting the alphabet.
	/// When the alphabet is exhausted and all possible sqids for this input are blocked
	/// [Error::BlocklistMaxAttempts] is returned.
	pub fn encode(&self, numbers: &[u64]) -> Result<String> {
		let mut encoder = self.encoder();
		encoder.encode(numbers)?;
		Ok(encoder.into_id())
	}

	fn encoder(&self) -> Encoder {
		Encoder::new(self)
	}

	/// Decode a sqid into a vector of numbers. When an invalid sqid is encountered an empty vector
	/// is returned.
	pub fn decode(&self, id: &str) -> Vec<u64> {
		let mut decoder = self.decoder();
		decoder.decode(id);
		decoder.into_numbers()
	}

	fn decoder(&self) -> Decoder {
		Decoder::new(self)
	}

	fn shuffle(chars: &mut [u8]) {
		for i in 0..(chars.len() - 1) {
			let j = chars.len() - 1 - i;
			let r = (i as u32 * j as u32 + chars[i] as u32 + chars[j] as u32) % chars.len() as u32;
			chars.swap(i, r as usize);
		}
	}
}

struct Encoder<'a> {
	base_alphabet: &'a [u8],
	current_alphabet: Vec<u8>,
	min_length: u8,
	blocklist: &'a HashSet<Vec<u8>>,
	id: Vec<u8>,
}

impl Encoder<'_> {
	fn new(sqids: &Sqids) -> Encoder {
		Encoder {
			base_alphabet: &sqids.alphabet,
			current_alphabet: Vec::new(),
			min_length: sqids.min_length,
			blocklist: &sqids.blocklist,
			id: Vec::new(),
		}
	}

	fn encode(&mut self, numbers: &[u64]) -> Result<()> {
		self.id.clear();

		if numbers.is_empty() {
			return Ok(());
		}

		for increment in 0..self.base_alphabet.len() {
			self.encode_numbers(numbers, increment)?;

			if !self.is_blocked_id(&self.id) {
				return Ok(());
			}
		}

		self.id.clear();
		Err(Error::BlocklistMaxAttempts)
	}

	fn encode_numbers(&mut self, numbers: &[u64], increment: usize) -> Result<()> {
		let mut offset = numbers.iter().enumerate().fold(numbers.len(), |a, (i, &v)| {
			self.base_alphabet[v as usize % self.base_alphabet.len()] as usize + i + a
		}) % self.base_alphabet.len();

		offset = (offset + increment) % self.base_alphabet.len();

		self.current_alphabet.clear();
		self.current_alphabet.extend_from_slice(&self.base_alphabet[offset..]);
		self.current_alphabet.extend_from_slice(&self.base_alphabet[..offset]);

		self.id.clear();
		self.id.push(self.current_alphabet[0]);

		self.current_alphabet.reverse();

		for (i, &num) in numbers.iter().enumerate() {
			self.encode_number(num);

			if i < numbers.len() - 1 {
				self.id.push(self.current_alphabet[0]);
				Sqids::shuffle(&mut self.current_alphabet);
			}
		}

		if self.min_length as usize > self.id.len() {
			self.id.push(self.current_alphabet[0]);

			while self.min_length as usize - self.id.len() > 0 {
				Sqids::shuffle(&mut self.current_alphabet);

				let slice_len =
					min(self.min_length as usize - self.id.len(), self.current_alphabet.len());
				let slice = &self.current_alphabet[..slice_len];

				self.id.extend(slice);
			}
		}

		Ok(())
	}

	fn encode_number(&mut self, num: u64) {
		let alphabet = &self.current_alphabet[1..];
		let mut result = num;
		let end = self.id.len();

		loop {
			let idx = (result % alphabet.len() as u64) as usize;
			self.id.push(alphabet[idx]);
			result /= alphabet.len() as u64;

			if result == 0 {
				break;
			}
		}

		self.id[end..].reverse();
	}

	fn is_blocked_id(&self, id: &[u8]) -> bool {
		let id: Vec<u8> = id.iter().map(u8::to_ascii_lowercase).collect();

		for word in self.blocklist {
			if word.len() <= id.len() {
				if id.len() <= 3 || word.len() <= 3 {
					if id == *word {
						return true;
					}
				} else if word.iter().any(|c| c.is_ascii_digit()) {
					if id.starts_with(word) || id.ends_with(word) {
						return true;
					}
				} else if id.windows(word.len()).any(|w| w == word) {
					return true;
				}
			}
		}

		false
	}

	fn into_id(self) -> String {
		String::from_utf8(self.id).expect("non-utf8 character encountered")
	}
}

struct Decoder<'a> {
	alphabet: &'a [u8],
	numbers: Vec<u64>,
}

impl Decoder<'_> {
	fn new(sqids: &Sqids) -> Decoder {
		Decoder { alphabet: &sqids.alphabet, numbers: Vec::new() }
	}

	pub fn decode(&mut self, id: &str) {
		self.numbers.clear();

		if id.is_empty() {
			return;
		}

		let alphabet_chars: HashSet<char> = self.alphabet.iter().cloned().map(char::from).collect();
		if !id.chars().all(|c| alphabet_chars.contains(&c)) {
			return;
		}

		let id = id.as_bytes();
		let prefix = id[0];
		let offset = self.alphabet.iter().position(|&c| c == prefix).unwrap();
		let mut alphabet: Vec<u8> = self.alphabet.to_vec();
		alphabet.rotate_left(offset);
		alphabet.reverse();

		let id = &id[1..];
		let separator = Cell::new(alphabet[0]);

		for chunk in id.split(|c| *c == separator.get()) {
			if chunk.is_empty() {
				return;
			}

			let alphabet_without_separator = &alphabet[1..];
			self.decode_number(chunk, alphabet_without_separator);

			Sqids::shuffle(&mut alphabet);
			separator.set(alphabet[0]);
		}
	}

	fn decode_number(&mut self, id: &[u8], alphabet: &[u8]) {
		let mut result = 0;

		for c in id {
			let idx = alphabet.iter().position(|x| x == c).unwrap();
			result = result * alphabet.len() as u64 + idx as u64;
		}

		self.numbers.push(result)
	}

	fn into_numbers(self) -> Vec<u64> {
		self.numbers
	}
}
