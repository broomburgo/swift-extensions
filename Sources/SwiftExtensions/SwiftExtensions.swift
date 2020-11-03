// MARK: - Functions & Operators

public func when<A>(_ condition: Bool, then ifTrue: () -> A, else ifFalse: () -> A) -> A {
  if condition {
    return ifTrue()
  } else {
    return ifFalse()
  }
}

public func optionally<A>(_ condition: Bool, then ifTrue: () -> A) -> A? {
  if condition {
    return ifTrue()
  } else {
    return nil
  }
}

public func absurd<A>(_ never: Never) -> A {}

precedencegroup FunctionApplicationPrecedence {
  associativity: left
  lowerThan: NilCoalescingPrecedence
  higherThan: ComparisonPrecedence
}

infix operator |>: FunctionApplicationPrecedence
infix operator &>: FunctionApplicationPrecedence

public func |> <Input, Output>(value: Input, function: (Input) throws -> Output) rethrows -> Output {
  try function(value)
}

public func &> <Input>(value: Input, function: (inout Input) throws -> Void) rethrows -> Input {
  var m_value = value
  try function(&m_value)
  return m_value
}

precedencegroup ForwardFunctionCompositionPrecedence {
  associativity: left
  lowerThan: TernaryPrecedence
  higherThan: FunctionArrowPrecedence
}

infix operator >>>: ForwardFunctionCompositionPrecedence

public func >>> <A, B>(
  lhs: @escaping () -> A,
  rhs: @escaping (A) -> B
) -> () -> B {
  { rhs(lhs()) }
}

public func >>> <A, B, C>(
  lhs: @escaping (A) -> B,
  rhs: @escaping (B) -> C
) -> (A) -> C {
  { a in rhs(lhs(a)) }
}

public func >>> <A, B, C>(
  lhs: @escaping (A) throws -> B,
  rhs: @escaping (B) -> C
) -> (A) throws -> C {
  { a in try rhs(lhs(a)) }
}

public func >>> <A, B, C>(
  lhs: @escaping (A) -> B,
  rhs: @escaping (B) throws -> C
) -> (A) throws -> C {
  { a in try rhs(lhs(a)) }
}

public func >>> <A, B, C>(
  lhs: @escaping (A) throws -> B,
  rhs: @escaping (B) throws -> C
) -> (A) throws -> C {
  { a in try rhs(lhs(a)) }
}

infix operator >>>=: AssignmentPrecedence

public func >>>= <A>(
  lhs: inout () -> A,
  rhs: @escaping (A) -> A
) {
  lhs = lhs >>> rhs
}

public func >>>= <A, B>(
  lhs: inout (A) -> B,
  rhs: @escaping (B) -> B
) {
  lhs = lhs >>> rhs
}

precedencegroup BackwardFunctionCompositionPrecedence {
  associativity: right
  lowerThan: TernaryPrecedence
  higherThan: FunctionArrowPrecedence
}

infix operator <<<: BackwardFunctionCompositionPrecedence

public func <<< <A, B, C>(
  lhs: @escaping (B) -> C,
  rhs: @escaping (A) -> B
) -> (A) -> C {
  { a in lhs(rhs(a)) }
}

public func <<< <A, B, C>(
  lhs: @escaping (B) throws -> C,
  rhs: @escaping (A) -> B
) -> (A) throws -> C {
  { a in try lhs(rhs(a)) }
}

public func <<< <A, B, C>(
  lhs: @escaping (B) -> C,
  rhs: @escaping (A) throws -> B
) -> (A) throws -> C {
  { a in try lhs(rhs(a)) }
}

public func <<< <A, B, C>(
  lhs: @escaping (B) throws -> C,
  rhs: @escaping (A) throws -> B
) -> (A) throws -> C {
  { a in try lhs(rhs(a)) }
}

infix operator <<<=: AssignmentPrecedence

public func <<<= <A, B>(
  lhs: inout (A) -> B,
  rhs: @escaping (A) -> A
) {
  lhs = lhs <<< rhs
}

// MARK: - Func

public struct Func<Input, Output> {
  public var run: (Input) -> Output

  public init(_ run: @escaping (Input) -> Output) {
    self.run = run
  }
}

public protocol FuncRepresentable {
  associatedtype Input
  associatedtype Output

  var funcValue: Func<Input, Output> { get }
  init(funcValue: Func<Input, Output>)
}

extension FuncRepresentable {
  public func callAsFunction(_ input: Input) -> Output {
    funcValue.run(input)
  }

  public mutating func append(_ transform: @escaping (inout Output) -> Void) {
    let current = funcValue
    self = Self(
      funcValue: Func { (input: Input) -> Output in
        var output = current.run(input)
        transform(&output)
        return output
      }
    )
  }

  public func appending(_ transform: @escaping (inout Output) -> Void) -> Self {
    self &> {
      $0.append(transform)
    }
  }
}

extension FuncRepresentable where Input == Void {
  public func callAsFunction() -> Output {
    funcValue.run(())
  }
}

extension Func: FuncRepresentable {
  public var funcValue: Func<Input, Output> {
    self
  }

  public init(funcValue: Func<Input, Output>) {
    self = funcValue
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

  public func unwrapOr(_ fallback: () -> Wrapped) -> Wrapped {
    whenSome(self) {
      $0
    } else: {
      fallback()
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
  case let .success(value):
    return ifSuccess(value)

  case let .failure(error):
    return ifFailure(error)
  }
}

extension Result {
  public func filter(
    _ condition: (Success) -> Bool,
    orFailWith getError: (Success) -> Failure
  ) -> Self {
    switch self {
    case let .success(value):
      return when(condition(value)) {
        self
      } else: {
        .failure(getError(value))
      }

    default:
      return self
    }
  }

  public func or(_ getFallback: () -> Self) -> Self {
    flatMapError { _ in getFallback() }
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

  public func getSuccessOr(_ fallback: (Failure) -> Success) -> Success {
    whenSuccess(self) {
      $0
    } else: {
      fallback($0)
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

extension Hashable {
  public func subscripting<Value>(_ dict: [Self: Value]) -> Value? {
    dict[self]
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

  /// Dual of the `contains` method on `ClosedRange`.
  public func isContained(in range: ClosedRange<Self>) -> Bool {
    range.contains(self)
  }

  /// Dual of the `contains` method on `Range`.
  public func isContained(in range: Range<Self>) -> Bool {
    range.contains(self)
  }
}

extension Collection {
  public var decomposed: (first: Element, rest: DropFirstSequence<Self>)? {
    first.map { ($0, dropFirst()) }
  }
}

extension RandomAccessCollection {
  public subscript(safely index: Index) -> Element? {
    guard indices.contains(index) else { return nil }
    return self[index]
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

  public func modify(update: (inout Value) -> Void) {
    var current = get()
    update(&current)
    set(current)
  }

  public func pullback<Subvalue>(_ keyPath: WritableKeyPath<Value, Subvalue>) -> Accessor<Subvalue> {
    Accessor<Subvalue> {
      self.get()[keyPath: keyPath]
    } set: {
      var value = self.get()
      value[keyPath: keyPath] = $0
      self.set(value)
    }
  }
}

public struct FailableAccessor<Value> {
  public var get: () throws -> Value
  public var set: (Value) throws -> Void

  public init(
    get: @escaping () throws -> Value,
    set: @escaping (Value) throws -> Void
  ) {
    self.get = get
    self.set = set
  }

  public init(initial: Value) {
    var value = initial
    self.init(
      get: { value },
      set: { value = $0; return () }
    )
  }

  public func modify(update: (inout Value) -> Void) throws {
    var current = try get()
    update(&current)
    try set(current)
  }

  public func pullback<Subvalue>(_ keyPath: WritableKeyPath<Value, Subvalue>) -> FailableAccessor<Subvalue> {
    FailableAccessor<Subvalue> {
      try self.get()[keyPath: keyPath]
    } set: {
      var value = try self.get()
      value[keyPath: keyPath] = $0
      try self.set(value)
    }
  }
}

extension Accessor {
  public init(failable: FailableAccessor<Value>, recover: @escaping () -> Value) {
    self.init {
      (try? failable.get()) ?? recover()
    } set: {
      try? failable.set($0)
    }
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

// MARK: - Unit

/// The `Unit` type, completely equivalent to `Void`, but useful for `Equatable`, `Hashable` and `Codable` purposes.
public struct Unit: Hashable, Codable {
  public func to<A>(_ value: A) -> A {
    value
  }
}

public let unit = Unit()
