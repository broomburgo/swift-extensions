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

// MARK: - Atomic

/// Masks `DispatchQueue`, without requiring `Foundation`.
///
/// Requires serial execution of work.
public protocol Synchronized {
  func sync<Output>(execute: () throws -> Output) rethrows -> Output
}

/// Wraps a mutable value and ensures atomic access to it.
///
/// source: https://www.objc.io/blog/2018/12/18/atomic-variables/
public final class Atomic<Queue: Synchronized, Wrapped> {
  private let queue: Queue
  private var value: Wrapped

  public init(queue: Queue, value: Wrapped) {
    self.queue = queue
    self.value = value
  }

  public var get: Wrapped {
    queue.sync { value }
  }

  public func modify(_ transform: (inout Wrapped) -> Void) {
    queue.sync {
      transform(&value)
    }
  }
}

// MARK: - Bool

public func when<A>(_ condition: Bool, then ifTrue: () -> A, else ifFalse: () -> A) -> A {
  if condition {
    return ifTrue()
  } else {
    return ifFalse()
  }
}

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

// MARK: - Deriving

public protocol DerivingEquatable: Equatable {
  associatedtype EquatableSource: Equatable

  var equatableSource: EquatableSource { get }
}

extension DerivingEquatable {
  public static func == (lhs: Self, rhs: Self) -> Bool {
    lhs.equatableSource == rhs.equatableSource
  }
}

public protocol DerivingHashable: Hashable {
  associatedtype HashableSource: Hashable

  var hashableSource: HashableSource { get }
}

extension DerivingHashable {
  public var hashValue: Int {
    hashableSource.hashValue
  }

  public func hash(into hasher: inout Hasher) {
    hashableSource.hash(into: &hasher)
  }
}

public protocol DerivingEncodable: Encodable {
  associatedtype EncodableSource: Encodable

  var encodableSource: EncodableSource { get }
}

extension DerivingEncodable {
  public func encode(to encoder: Encoder) throws {
    try encodableSource.encode(to: encoder)
  }
}

public protocol DerivingDecodable: Decodable {
  associatedtype DecodableSource: Decodable

  init(decodableSource: DecodableSource)
}

extension DerivingDecodable {
  public init(from decoder: Decoder) throws {
    self.init(decodableSource: try DecodableSource(from: decoder))
  }
}

public typealias DerivingCodable = DerivingEncodable & DerivingDecodable

public protocol DerivingCollection: Collection where
  Index == CollectionSource.Index,
  Element == CollectionSource.Element {
  associatedtype CollectionSource: Collection

  var collectionSource: CollectionSource { get }
}

extension DerivingCollection {
  public var startIndex: Index {
    collectionSource.startIndex
  }

  public var endIndex: Index {
    collectionSource.endIndex
  }

  public subscript(position: Index) -> Element {
    collectionSource[position]
  }

  public func index(after i: Index) -> Index {
    collectionSource.index(after: i)
  }
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

// MARK: - Operators

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

public func absurd<A>(_ never: Never) -> A {}

// MARK: - Optional

public func whenSome<A, B>(_ value: A?, then ifSome: (A) -> B, else ifNone: () -> B) -> B {
  switch value {
  case let .some(x):
    return ifSome(x)

  case .none:
    return ifNone()
  }
}

public func optionally<A>(_ condition: Bool, then ifTrue: () -> A) -> A? {
  if condition {
    return ifTrue()
  } else {
    return nil
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

// MARK: - Utility

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

extension String.StringInterpolation {
  public mutating func appendInterpolation<A>(_ optionalValue: A?, or defaultString: String) {
    guard let value = optionalValue else {
      appendInterpolation(defaultString)
      return
    }

    appendInterpolation(value)
  }
}
