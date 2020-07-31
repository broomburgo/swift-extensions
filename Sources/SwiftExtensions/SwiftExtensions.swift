// MARK: - Functions & Operators

public func when<A>(_ condition: Bool, then ifTrue: () -> A, else ifFalse: () -> A) -> A {
  if condition {
    return ifTrue()
  } else {
    return ifFalse()
  }
}

public func absurd<A>(_ never: Never) -> A {}

precedencegroup FunctionApplication {
  associativity: left
}

infix operator |>: FunctionApplication
infix operator &>: FunctionApplication

public func |> <Input, Output>(value: Input, function: (Input) throws -> Output) rethrows -> Output {
  try function(value)
}

public func &> <Input>(value: Input, function: (inout Input) throws -> Void) rethrows -> Input {
  var m_value = value
  try function(&m_value)
  return m_value
}

// MARK: - Func

public struct Func<Input, Output> {
  public let run: (Input) -> Output

  public init(_ run: @escaping (Input) -> Output) {
    self.run = run
  }

  public func callAsFunction(_ input: Input) -> Output {
    run(input)
  }
}

// MARK: - Optional

public func whenSome<A, B>(_ value: A?, then ifSome: (A) -> B, else ifNone: () -> B) -> B {
  switch value {
  case let .some(x):
    return ifSome(x)

  case .none:
    return ifNone()
  }
}

extension Optional {
  public func filter(_ condition: (Wrapped) -> Bool) -> Self {
    switch self {
    case let .some(value) where condition(value):
      return self

    default:
      return nil
    }
  }

  public func forEach(_ run: (Wrapped) -> Void) {
    whenSome(self) {
      run($0)
    } else: {
      /// ignore
    }
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

public func whenSuccess<A, E, B>(_ result: Result<A, E>, then ifSuccess: (A) -> B, else ifFailure: (E) -> B) -> B {
  switch result {
  case .success(let value):
    return ifSuccess(value)

  case .failure(let error):
    return ifFailure(error)
  }
}

extension Result {
  public func filter(
    _ condition: (Success) -> Bool,
    orFailWith getError: (Success) -> Failure
  ) -> Self {
    switch self {
    case .success(let value):
      return when(condition(value)) {
        self
      } else: {
        .failure(getError(value))
      }

    default:
      return self
    }
  }

  public var success: Success? {
    whenSuccess(self) {
      $0
    } else: { _ in
      nil
    }
  }

  public var failure: Failure? {
    whenSuccess(self) { _ in
      nil
    } else: {
      $0
    }
  }

  public var isSuccess: Bool {
    whenSuccess(self) { _ in
      true
    } else: { _ in
      false
    }
  }

  public var isFailure: Bool {
    whenSuccess(self) { _ in
      false
    } else: { _ in
      true
    }
  }

  public init(ifNotNil success: Success?, elseFailWith getError: @autoclosure () -> Failure) {
    self = whenSome(success) {
      .success($0)
    } else: {
      .failure(getError())
    }
  }
}

// MARK: .zipWith

extension Result {
  public static func zipWith<A, B, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ transform: (A, B) -> Final,
    mergeFailures: (Failure, Failure) -> Failure
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

  public static func zipWith<A, B, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ transform: (A, B) -> Final
  ) -> Result<Final, Failure> {
    zipWith(ra, rb) {
      transform($0, $1)
    } mergeFailures: { a, _ in
      a
    }
  }

  public static func zipWith<A, B, C, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ transform: (A, B, C) -> Final,
    mergeFailures: (Failure, Failure) -> Failure
  ) -> Result<Final, Failure> {
    zipWith(
      ra,
      zipWith(rb, rc, { ($0, $1) }, mergeFailures: mergeFailures),
      { a, bc in transform(a, bc.0, bc.1) },
      mergeFailures: mergeFailures
    )
  }

  public static func zipWith<A, B, C, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ transform: (A, B, C) -> Final
  ) -> Result<Final, Failure> {
    zipWith(ra, rb, rc) {
      transform($0, $1, $2)
    } mergeFailures: { a, _ in
      a
    }
  }

  public static func zipWith<A, B, C, D, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ rd: Result<D, Failure>,
    _ transform: (A, B, C, D) -> Final,
    mergeFailures: (Failure, Failure) -> Failure
  ) -> Result<Final, Failure> {
    zipWith(
      ra,
      zipWith(rb, rc, rd, { ($0, $1, $2) }, mergeFailures: mergeFailures),
      { a, bcd in transform(a, bcd.0, bcd.1, bcd.2) },
      mergeFailures: mergeFailures
    )
  }

  public static func zipWith<A, B, C, D, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ rd: Result<D, Failure>,
    _ transform: (A, B, C, D) -> Final
  ) -> Result<Final, Failure> {
    zipWith(ra, rb, rc, rd) {
      transform($0, $1, $2, $3)
    } mergeFailures: { a, _ in
      a
    }
  }

  public static func zipWith<A, B, C, D, E, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ rd: Result<D, Failure>,
    _ re: Result<E, Failure>,
    _ transform: (A, B, C, D, E) -> Final,
    mergeFailures: (Failure, Failure) -> Failure
  ) -> Result<Final, Failure> {
    zipWith(
      ra,
      zipWith(rb, rc, rd, re, { ($0, $1, $2, $3) }, mergeFailures: mergeFailures),
      { a, bcde in transform(a, bcde.0, bcde.1, bcde.2, bcde.3) },
      mergeFailures: mergeFailures
    )
  }

  public static func zipWith<A, B, C, D, E, Final>(
    _ ra: Result<A, Failure>,
    _ rb: Result<B, Failure>,
    _ rc: Result<C, Failure>,
    _ rd: Result<D, Failure>,
    _ re: Result<E, Failure>,
    _ transform: (A, B, C, D, E) -> Final
  ) -> Result<Final, Failure> {
    zipWith(ra, rb, rc, rd, re) {
      transform($0, $1, $2, $3, $4)
    } mergeFailures: { a, _ in
      a
    }
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
}

// MARK: - Utility

extension String.StringInterpolation {
  public mutating func appendInterpolation<A>(_ optionalValue: A?, or defaultString: String) {
    guard let value = optionalValue else {
      appendInterpolation(defaultString)
      return
    }

    appendInterpolation(value)
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

// MARK: - Wrapper

public protocol Wrapper {
  associatedtype Wrapped
  var wrapped: Wrapped { get }
}

public protocol InitializableWrapper: Wrapper {
  init(_ wrapped: Wrapped)
}

extension Wrapper {
  public subscript<A>(dynamicMember keyPath: KeyPath<Wrapped, A>) -> A {
    wrapped[keyPath: keyPath]
  }
}

extension InitializableWrapper where Wrapped: Decodable {
  public init(from decoder: Decoder) throws {
    try self.init(Wrapped(from: decoder))
  }
}

extension Wrapper where Wrapped: Encodable {
  public func encode(to encoder: Encoder) throws {
    try wrapped.encode(to: encoder)
  }
}

extension Wrapper where Wrapped: Collection {
  public typealias Index = Wrapped.Index
  public typealias Element = Wrapped.Element

  public var startIndex: Index {
    wrapped.startIndex
  }

  public var endIndex: Index {
    wrapped.endIndex
  }

  public subscript(position: Index) -> Element {
    wrapped[position]
  }

  public func index(after i: Index) -> Index {
    wrapped.index(after: i)
  }
}
