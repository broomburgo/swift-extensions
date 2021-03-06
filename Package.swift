// swift-tools-version:5.2
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
  name: "swift-extensions",
  products: [
    .library(
      name: "SwiftExtensions",
      targets: ["SwiftExtensions"]
    ),
  ],
  targets: [
    .target(
      name: "SwiftExtensions"
    ),
    .testTarget(
      name: "SwiftExtensionsTests",
      dependencies: ["SwiftExtensions"]
    ),
  ]
)
