// MARK: - Boolean

precedencegroup LogicalImplicationPrecedence {
  associativity: right
  higherThan: TernaryPrecedence
  lowerThan: LogicalDisjunctionPrecedence
}

infix operator =>: LogicalImplicationPrecedence

public extension Bool {
  static func => (_ lhs: Bool, _ rhs: @autoclosure () -> Bool) -> Bool {
    !lhs || rhs()
  }

  var not: Bool {
    !self
  }
}

// MARK: - Deriving

public protocol DerivingEquatable: Equatable {
  associatedtype EquatableSource: Equatable

  var equatableSource: EquatableSource { get }
}

public extension DerivingEquatable {
  static func == (lhs: Self, rhs: Self) -> Bool {
    lhs.equatableSource == rhs.equatableSource
  }
}

public protocol DerivingHashable: Hashable {
  associatedtype HashableSource: Hashable

  var hashableSource: HashableSource { get }
}

public extension DerivingHashable {
  var hashValue: Int {
    hashableSource.hashValue
  }

  func hash(into hasher: inout Hasher) {
    hashableSource.hash(into: &hasher)
  }
}

public protocol DerivingEncodable: Encodable {
  associatedtype EncodableSource: Encodable

  var encodableSource: EncodableSource { get }
}

public extension DerivingEncodable {
  func encode(to encoder: Encoder) throws {
    try encodableSource.encode(to: encoder)
  }
}

public protocol DerivingDecodable: Decodable {
  associatedtype DecodableSource: Decodable

  init(decodableSource: DecodableSource)
}

public extension DerivingDecodable {
  init(from decoder: Decoder) throws {
    self.init(decodableSource: try DecodableSource(from: decoder))
  }
}

public typealias DerivingCodable = DerivingEncodable & DerivingDecodable

public protocol DerivingCollection: Collection where
  Index == CollectionSource.Index,
  Element == CollectionSource.Element
{
  associatedtype CollectionSource: Collection

  var collectionSource: CollectionSource { get }
}

public extension DerivingCollection {
  var startIndex: Index {
    collectionSource.startIndex
  }

  var endIndex: Index {
    collectionSource.endIndex
  }

  subscript(position: Index) -> Element {
    collectionSource[position]
  }

  func index(after i: Index) -> Index {
    collectionSource.index(after: i)
  }
}

// MARK: - Lens

@dynamicMemberLookup
public struct Lens<Value> {
  private var get: () -> Value
  private var set: (Value) -> Void

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

// MARK: - Optional

public func optionally<A>(_ condition: Bool, then ifTrue: () -> A) -> A? {
  if condition {
    return ifTrue()
  } else {
    return nil
  }
}

public extension Optional {
  func filter(_ condition: (Wrapped) -> Bool) -> Self {
    guard let wrapped = self, condition(wrapped) else {
      return nil
    }

    return self
  }
}

// MARK: - Result

public extension Result {
  func filter(
    _ condition: (Success) -> Bool,
    orFailWith getError: (Success) -> Failure
  ) -> Self {
    guard case .success(let value) = self, condition(value) else {
      return flatMap {
        .failure(getError($0))
      }
    }

    return self
  }

  func getSuccessOr(_ fallback: (Failure) -> Success) -> Success {
    switch self {
    case .success(let value):
      return value

    case .failure(let error):
      return fallback(error)
    }
  }
}

// MARK: - Collections

public extension Equatable {
  /// Dual of the `contains` method on `Sequence`.
  func isContained<S: Sequence>(in s: S) -> Bool where S.Element == Self {
    s.contains(self)
  }
}

public extension Hashable {
  func subscripting<Value>(_ dict: [Self: Value]) -> Value? {
    dict[self]
  }
}

public extension Comparable {
  func clamped(in range: ClosedRange<Self>) -> Self {
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
  func isContained(in range: ClosedRange<Self>) -> Bool {
    range.contains(self)
  }

  /// Dual of the `contains` method on `Range`.
  func isContained(in range: Range<Self>) -> Bool {
    range.contains(self)
  }
}

public extension Collection {
  var decomposed: (first: Element, rest: DropFirstSequence<Self>)? {
    first.map { ($0, dropFirst()) }
  }
}

public extension BidirectionalCollection {
  var decomposedLast: (last: Element, rest: [Element])? {
    last.map { ($0, dropLast()) }
  }
}

public extension RandomAccessCollection {
  subscript(safely index: Index) -> Element? {
    guard indices.contains(index) else { return nil }
    return self[index]
  }
}

// MARK: - StringInterpolation

public extension String.StringInterpolation {
  mutating func appendInterpolation<A>(_ optionalValue: A?, or defaultString: String) {
    guard let value = optionalValue else {
      appendInterpolation(defaultString)
      return
    }

    appendInterpolation(value)
  }
}

// MARK: - Synchronous/Asynchronous

/// Masks `DispatchQueue.sync`, without requiring `Foundation`.
///
/// Conform with:
/// ```
/// extension DispatchQueue: Synchronous {
///   public func runSync<Output>(_ execute: () throws -> Output) rethrows -> Output {
///     try sync(execute: execute)
///   }
/// }
/// ```
public protocol Synchronous {
  func runSync<Output>(_: () throws -> Output) rethrows -> Output
}

/// Masks `DispatchQueue.async`, without requiring `Foundation`.
///
/// Requires serial execution of work.
///
/// Conform with:
/// ```
/// extension DispatchQueue: Asynchronous {
///   public func runAsync(_ execute: () -> Void) {
///     async(execute: execute)
///   }
/// }
/// ```
public protocol Asynchronous {
  func runAsync(_: @escaping () -> Void)
}

// MARK: - Atomic

/// Wraps a mutable value and ensures atomic access to it.
///
/// source: https://www.objc.io/blog/2018/12/18/atomic-variables/
public final class Atomic<Queue: Synchronous, Wrapped> {
  private let queue: Queue
  private var value: Wrapped

  public init(queue: Queue, value: Wrapped) {
    self.queue = queue
    self.value = value
  }

  public var get: Wrapped {
    queue.runSync { value }
  }

  public func mutate(_ transform: (inout Wrapped) -> Void) {
    queue.runSync {
      transform(&value)
    }
  }
}

// MARK: - Async

/// While waiting for async/await, this will do.
public struct Async<Success> {
  private var _run: (@escaping (Result<Success, Error>) -> Void) -> Void

  public init(run: @escaping (@escaping (Result<Success, Error>) -> Void) -> Void) {
    self._run = run
  }

  public init(_ result: Result<Success, Error>) {
    self.init { yield in
      yield(result)
    }
  }

  public func run(_ callback: @escaping (Result<Success, Error>) -> Void) {
    _run(callback)
  }
}

public extension Async {
  func map<NewSuccess>(
    _ transform: @escaping (Success) -> NewSuccess
  ) -> Async<NewSuccess> {
    Async<NewSuccess> { yield in
      self._run {
        yield(
          $0.map(transform)
        )
      }
    }
  }

  func flatMap<NewSuccess>(
    _ transform: @escaping (Success) -> Async<NewSuccess>
  ) -> Async<NewSuccess> {
    Async<NewSuccess> { yield in
      self._run {
        switch $0 {
        case .success(let value):
          transform(value)._run(yield)

        case .failure(let error):
          yield(.failure(error))
        }
      }
    }
  }

  func flatMapError(
    _ transform: @escaping (Error) -> Async<Success>
  ) -> Self {
    Async { yield in
      self._run {
        switch $0 {
        case .success(let value):
          yield(.success(value))

        case .failure(let error):
          transform(error)._run(yield)
        }
      }
    }
  }

  func filter(
    _ condition: @escaping (Success) -> Bool,
    orFailWith getError: @escaping (Success) -> Error
  ) -> Self {
    flatMap {
      if condition($0) {
        return Async(.success($0))
      } else {
        return Async(.failure(getError($0)))
      }
    }
  }

  func zipWith<OtherSuccess, FinalSuccess>(
    _ other: Async<OtherSuccess>,
    transform: @escaping (Success, OtherSuccess) -> FinalSuccess,
    uniquingErrorsWith mergeErrors: @escaping (Error, Error) -> Error = { first, _ in first }
  ) -> Async<FinalSuccess> {
    Async<FinalSuccess> { yield in
      var resultSelf: Result<Success, Error>? {
        didSet {
          yieldIfPossible(resultSelf, resultOther)
        }
      }

      var resultOther: Result<OtherSuccess, Error>? {
        didSet {
          yieldIfPossible(resultSelf, resultOther)
        }
      }

      self._run {
        resultSelf = $0
      }

      other._run {
        resultOther = $0
      }

      func yieldIfPossible(_ t1Result: Result<Success, Error>?, _ t2Result: Result<OtherSuccess, Error>?) {
        guard
          let t1Result = t1Result,
          let t2Result = t2Result
        else {
          return
        }

        switch (t1Result, t2Result) {
        case (.success(let value1), .success(let value2)):
          yield(.success(transform(value1, value2)))

        case (.failure(let error1), .failure(let error2)):
          yield(.failure(mergeErrors(error1, error2)))

        case (.failure(let error), .success(_)),
             (.success(_), .failure(let error)):
          yield(.failure(error))
        }
      }
    }
  }

  func zipWithAll<FinalSuccess>(
    in rest: [Self],
    transform: @escaping ([Success]) -> FinalSuccess,
    uniquingErrorsWith mergeErrors: @escaping (Error, Error) -> Error = { first, _ in first }
  ) -> Async<FinalSuccess> {
    rest
      .reduce(map { [$0] }) {
        $0.zipWith($1) {
          var m = $0
          m.append($1)
          return m
        } uniquingErrorsWith: {
          mergeErrors($0, $1)
        }
      }
      .map {
        transform($0)
      }
  }

  func onResult(_ callback: @escaping (Result<Success, Error>) -> Void) -> Self {
    Async { yield in
      self._run {
        callback($0)
        yield($0)
      }
    }
  }

  func onSuccess(_ callback: @escaping (Success) -> Void) -> Self {
    onResult {
      guard case .success(let value) = $0 else {
        return
      }

      callback(value)
    }
  }

  func onFailure(_ callback: @escaping (Error) -> Void) -> Self {
    onResult {
      guard case .failure(let error) = $0 else {
        return
      }

      callback(error)
    }
  }

  func receive(on asynchronous: Asynchronous) -> Self {
    Async { yield in
      self._run { result in
        asynchronous.runAsync {
          yield(result)
        }
      }
    }
  }
}

public extension Async where Success == Void {
  static let succeeded = Async(.success(()))
}
