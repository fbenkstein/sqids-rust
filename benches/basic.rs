use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use sqids::Sqids;
use std::{collections::hash_map::DefaultHasher, hash::Hasher};

fn bench_create(c: &mut Criterion) {
	let mut group = c.benchmark_group("create");
	group.bench_function("create", |b| b.iter(|| black_box(Sqids::builder()).build()));
	group.finish();
}

#[derive(Debug)]
struct Input {
	numbers: Vec<u64>,
	parameter_id: String,
}

fn inputs() -> Vec<Input> {
	let mut inputs = Vec::new();

	inputs.push(Input { numbers: vec![], parameter_id: "[]".to_string() });

	inputs.extend(
		(0..u64::BITS)
			.step_by(8)
			.map(|i| 1 << i)
			.chain([u64::MAX])
			.map(|n| Input { numbers: vec![n], parameter_id: format!("[{n}]") }),
	);

	for l in [2, 4, 8, 16, 32] {
		let mut hasher = DefaultHasher::new();
		inputs.push(Input {
			numbers: (0..l)
				.map(|i| {
					hasher.write_u32(i);
					hasher.finish()
				})
				.collect(),
			parameter_id: format!("[x; {l}]"),
		});
	}

	inputs
}

fn bench_encode(c: &mut Criterion) {
	let sqids = Sqids::default();

	let mut group = c.benchmark_group("encode");

	for Input { numbers, ref parameter_id } in inputs() {
		let id = sqids.encode(&numbers).unwrap();
		group.throughput(criterion::Throughput::Bytes(id.len() as u64));

		group.bench_with_input(
			BenchmarkId::new("Sqids::encode", parameter_id),
			&numbers,
			|b, x| b.iter(|| sqids.encode(black_box(x))),
		);

		let mut encoder = sqids.encoder();
		group.bench_with_input(
			BenchmarkId::new("Encoder::encode", parameter_id),
			&numbers,
			|b, x| {
				b.iter(|| {
					let _ = encoder.encode(black_box(x));
				})
			},
		);
	}

	group.finish();
}

fn bench_decode(c: &mut Criterion) {
	let sqids = Sqids::default();

	let mut group = c.benchmark_group("decode");

	for Input { numbers, ref parameter_id } in inputs() {
		let id = sqids.encode(&numbers).unwrap();
		group.throughput(criterion::Throughput::Bytes(id.len() as u64));

		group.bench_with_input(BenchmarkId::new("Squids::decode", parameter_id), &id, |b, x| {
			b.iter(|| sqids.decode(black_box(x)))
		});

		let mut decoder = sqids.decoder();
		group.bench_with_input(BenchmarkId::new("Decoder::decode", parameter_id), &id, |b, x| {
			b.iter(|| {
				let _ = decoder.decode(black_box(x));
			})
		});
	}

	group.finish();
}

criterion_group!(benches, bench_create, bench_encode, bench_decode);
criterion_main!(benches);
