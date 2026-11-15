import path from "node:path";
import type { NextConfig } from "next";

// Empty for a local build and for a user site. GitHub Pages sets
// PAGES_BASE_PATH to the project path, for example /eml-and-one.
const basePath = process.env.PAGES_BASE_PATH || process.env.BASE_PATH || "";

const nextConfig: NextConfig = {
  output: "export",
  trailingSlash: true,
  basePath,
  assetPrefix: basePath === "" ? undefined : basePath,
  // This directory can sit inside another project that also has a lockfile.
  // The site root is this directory, not that parent.
  turbopack: { root: path.join(__dirname) },
};

export default nextConfig;
