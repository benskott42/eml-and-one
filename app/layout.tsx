import type { Metadata } from "next";
import { EARLY_KEY_SCRIPT } from "@/components/calculator/earlyKeys";
import "./globals.css";

const basePath = process.env.PAGES_BASE_PATH || process.env.BASE_PATH || "";

export const metadata: Metadata = {
  applicationName: "EML and One",
  title: "EML and One",
  description: "a two-button calculator",
  icons: {
    icon: [
      { url: `${basePath}/icon-192.png`, sizes: "192x192", type: "image/png" },
      { url: `${basePath}/icon-512.png`, sizes: "512x512", type: "image/png" },
    ],
    apple: [{ url: `${basePath}/apple-touch-icon.png`, sizes: "180x180", type: "image/png" }],
  },
  openGraph: {
    title: "EML and One",
    description: "a two-button calculator",
    siteName: "EML and One",
  },
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <head>
        <script dangerouslySetInnerHTML={{ __html: EARLY_KEY_SCRIPT }} />
      </head>
      <body>{children}</body>
    </html>
  );
}
