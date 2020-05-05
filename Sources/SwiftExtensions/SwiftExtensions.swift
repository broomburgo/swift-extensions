// MARK: - Functions

public func absurd<A>(_ never: Never) -> A {}

public struct Func<Input, Output> {
  public var run: (Input) -> Output

  public init(_ run: @escaping (Input) -> Output) {
    self.run = run
  }

  public func callAsFunction(_ input: Input) -> Output {
    run(input)
  }
}

// MARK: - Optional

extension Optional {
  public func filter(_ condition: (Wrapped) -> Bool) -> Self {
    flatMap {
      condition($0) ? .some($0) : .none
    }
  }

  public func fold<A>(onSome: (Wrapped) -> A, onNone: () -> A) -> A {
    switch self {
    case let .some(x):
      return onSome(x)

    case .none:
      return onNone()
    }
  }

  public func forEach(_ run: (Wrapped) -> Void) {
    fold(onSome: run, onNone: {})
  }
}

// MARK: .zipWith

extension Optional {
  public static func zipWith<A, B, Final>(
    _ oa: A?,
    _ ob: B?,
    _ transform: (A, B) -> Final
  ) -> Final? {
    switch (oa, ob) {
    case let (.some(a), .some(b)):
      return .some(transform(a, b))

    default:
      return nil
    }
  }

  public static func zipWith<A, B, C, Final>(
    _ oa: A?,
    _ ob: B?,
    _ oc: C?,
    _ transform: (A, B, C) -> Final
  ) -> Final? {
    zipWith(
      oa,
      zipWith(ob, oc) { ($0, $1) }
    ) { a, bc in
      transform(a, bc.0, bc.1)
    }
  }

  public static func zipWith<A, B, C, D, Final>(
    _ oa: A?,
    _ ob: B?,
    _ oc: C?,
    _ od: D?,
    _ transform: (A, B, C, D) -> Final
  ) -> Final? {
    zipWith(
      oa,
      zipWith(ob, oc, od) { ($0, $1, $2) }
    ) { a, bcd in
      transform(a, bcd.0, bcd.1, bcd.2)
    }
  }

  public static func zipWith<A, B, C, D, E, Final>(
    _ oa: A?,
    _ ob: B?,
    _ oc: C?,
    _ od: D?,
    _ oe: E?,
    _ transform: (A, B, C, D, E) -> Final
  ) -> Final? {
    zipWith(
      oa,
      zipWith(ob, oc, od, oe) { ($0, $1, $2, $3) }
    ) { a, bcde in
      transform(a, bcde.0, bcde.1, bcde.2, bcde.3)
    }
  }
}

// MARK: - Result

extension Result {
  public func filter(_ condition: (Success) -> Bool, orFailWith getError: (Success) -> Failure) -> Self {
    flatMap {
      condition($0) ? .success($0) : .failure(getError($0))
    }
  }

  public func fold<A>(onSuccess: (Success) -> A, onFailure: (Failure) -> A) -> A {
    switch self {
    case let .success(x):
      return onSuccess(x)

    case let .failure(x):
      return onFailure(x)
    }
  }

  public var successValue: Success? {
    fold(onSuccess: { $0 }, onFailure: { _ in nil })
  }

  public init(ifNotNil success: Success?, elseFailWith error: @autoclosure () -> Failure) {
    self = success.fold(
      onSome: { .success($0) },
      onNone: { .failure(error()) }
    )
  }
}

// MARK: .zipWith

extension Result {
  public static func zipWith<A, B, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ transform: (A, B) -> Final,
    mergeFailures: (Failure, Failure) -> Failure = { f, _ in f }
  ) -> Result<Final, Failure> {
    switch (ra, rb) {
    case let (.success(a), .success(b)):
      return .success(transform(a, b))

    case let (.failure(a), .failure(b)):
      return .failure(mergeFailures(a, b))

    case let (.failure(a), _):
      return .failure(a)

    case let (_, .failure(b)):
      return .failure(b)
    }
  }

  public static func zipWith<A, B, C, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ transform: (A, B, C) -> Final,
    mergeFailures: (Failure, Failure) -> Failure = { f, _ in f }
  ) -> Result<Final, Failure> {
    zipWith(
      ra,
      zipWith(rb, rc, { ($0, $1) }, mergeFailures: mergeFailures),
      { a, bc in transform(a, bc.0, bc.1) },
      mergeFailures: mergeFailures
    )
  }

  public static func zipWith<A, B, C, D, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ rd: Result<D, Failure>,
    _ transform: (A, B, C, D) -> Final,
    mergeFailures: (Failure, Failure) -> Failure = { f, _ in f }
  ) -> Result<Final, Failure> {
    zipWith(
      ra,
      zipWith(rb, rc, rd, { ($0, $1, $2) }, mergeFailures: mergeFailures),
      { a, bcd in transform(a, bcd.0, bcd.1, bcd.2) },
      mergeFailures: mergeFailures
    )
  }

  public static func zipWith<A, B, C, D, E, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ rd: Result<D, Failure>,
    _ re: Result<E, Failure>,
    _ transform: (A, B, C, D, E) -> Final,
    mergeFailures: (Failure, Failure) -> Failure = { f, _ in f }
  ) -> Result<Final, Failure> {
    zipWith(
      ra,
      zipWith(rb, rc, rd, re, { ($0, $1, $2, $3) }, mergeFailures: mergeFailures),
      { a, bcde in transform(a, bcde.0, bcde.1, bcde.2, bcde.3) },
      mergeFailures: mergeFailures
    )
  }
}

// MARK: - Sequences

extension Equatable {
  public func isContained<S: Sequence>(in s: S) -> Bool where S.Element == Self {
    s.contains(self)
  }
}

extension Comparable {
  public func clamped(in range: ClosedRange<Self>) -> Self {
    switch self {
    case ..<range.lowerBound:
      return range.lowerBound

    case range.upperBound...:
      return range.upperBound

    default:
      return self
    }
  }
}

extension Collection {
  public var decomposed: (head: Element, tail: DropFirstSequence<Self>)? {
    first.map { ($0, dropFirst()) }
  }
}

extension RandomAccessCollection {
  public subscript(safely index: Index) -> Element? {
    guard indices.contains(index) else { return nil }
    return self[index]
  }
}

extension RangeReplaceableCollection {
  public func appending(_ newElement: Element) -> Self {
    var this = self
    this.append(newElement)
    return this
  }
}

// MARK: - Bool

precedencegroup LogicalImplicationPrecedence {
  associativity: right
  higherThan: TernaryPrecedence
  lowerThan: LogicalDisjunctionPrecedence
}

infix operator =>: LogicalImplicationPrecedence

extension Bool {
  public static func => (_ lhs: Bool, _ rhs: @autoclosure () -> Bool) -> Bool {
    !lhs || rhs()
  }

  public var not: Bool {
    !self
  }

  public func fold<A>(onTrue: @autoclosure () -> A, onFalse: @autoclosure () -> A) -> A {
    self ? onTrue() : onFalse()
  }
}

// MARK: - Utility

extension String.StringInterpolation {
  public mutating func appendInterpolation<A>(_ optionalValue: A?, or defaultString: String) {
    guard let value = optionalValue else {
      appendLiteral(defaultString)
      return
    }

    appendLiteral("\(value)")
  }
}

// MARK: - Accessor

public struct Accessor<Value> {
  public var get: () -> Value
  public var set: (Value) -> Void

  public init(
    get: @escaping () -> Value,
    set: @escaping (Value) -> Void
  ) {
    self.get = get
    self.set = set
  }

  public init(initial: Value) {
    var value = initial
    self.init(
      get: { value },
      set: { value = $0 }
    )
  }
}
