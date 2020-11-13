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

// MARK: - Lens

@dynamicMemberLookup
public struct Lens<Value> {
  private let get: () -> Value
  private let set: (Value) -> Void

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

  public var value: Value {
    get {
      get()
    }
    nonmutating set {
      set(newValue)
    }
  }

  public subscript<NewValue>(dynamicMember keyPath: WritableKeyPath<Value, NewValue>) -> Lens<NewValue> {
    Lens<NewValue> {
      self.value[keyPath: keyPath]
    } set: {
      self.value[keyPath: keyPath] = $0
    }
  }
}

@dynamicMemberLookup
public struct ThrowingLens<Value> {
  private let get: () throws -> Value
  private let set: (Value) throws -> Void

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
      set: { value = $0 }
    )
  }

  public func callAsFunction() throws -> Value {
    try get()
  }

  public func callAsFunction(set newValue: Value) throws {
    try set(newValue)
  }

  public func callAsFunction(modify transform: (inout Value) -> Void) throws {
    var current = try get()
    transform(&current)
    try set(current)
  }

  public subscript<NewValue>(dynamicMember keyPath: WritableKeyPath<Value, NewValue>) -> ThrowingLens<NewValue> {
    ThrowingLens<NewValue> {
      try self()[keyPath: keyPath]
    } set: {
      var value = try self()
      value[keyPath: keyPath] = $0
      try self(set: value)
    }
  }
}

extension Lens {
  public init(throwing: ThrowingLens<Value>, recover: @escaping () -> Value) {
    self.init {
      (try? throwing()) ?? recover()
    } set: {
      try? throwing(set: $0)
    }
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
    case let value? where condition(value):
      return self

    default:
      return nil
    }
  }

  public func forEach(_ run: (Wrapped) -> Void) {
    guard let wrapped = self else {
      return
    }
    
    run(wrapped)
  }

  public func unwrapOr(_ fallback: () -> Wrapped) -> Wrapped {
    guard let wrapped = self else {
      return fallback()
    }
    
    return wrapped
  }
}

// MARK: - Result

extension Result {
  public func filter(
    _ condition: (Success) -> Bool,
    orFailWith getError: (Success) -> Failure
  ) -> Self {
    switch self {
    case .success(let value) where condition(value):
      return self

    default:
      return flatMap {
        .failure(getError($0))
      }
    }
  }
  
  public func or(_ getFallback: () -> Self) -> Self {
    flatMapError { _ in getFallback() }
  }
  
  public func getSuccessOr(_ fallback: (Failure) -> Success) -> Success {
    switch self {
    case .success(let value):
      return value
      
    case .failure(let error):
      return fallback(error)
    }
  }
  
  public func forSuccess(_ onSuccess: (Success) -> Void, failure onFailure: (Failure) -> Void) {
    switch self {
    case .success(let value):
      onSuccess(value)
    
    case .failure(let error):
      onFailure(error)
    }
  }

  public var isSuccess: Bool {
    switch self {
    case .success:
      return true
      
    case .failure:
      return false
    }
  }

  public var isFailure: Bool {
    isSuccess.not
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
