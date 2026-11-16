import type { MetadataRoute } from "next";

// Empty locally. GitHub Pages sets PAGES_BASE_PATH, for example /eml-and-one.
const basePath = process.env.PAGES_BASE_PATH || process.env.BASE_PATH || "";

export default function manifest(): MetadataRoute.Manifest {
  return {
    name: "EML and One",
    short_name: "EML and One",
    description: "a two-button calculator",
    start_url: `${basePath}/`,
    scope: `${basePath}/`,
    display: "standalone",
    orientation: "portrait",
    background_color: "#1c2126",
    theme_color: "#343b43",
  };
}
